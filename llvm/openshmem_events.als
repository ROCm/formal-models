module memory_consistency/llvm/openshmem_events

// OpenSHMEM API-level memory model: event and structural extensions.
//
// This module extends the base LLVM/C++ event model (events.als, memory.als,
// memory_ordering.als) with the additions from Step 1 and Step 2 of the
// OpenSHMEM API-level memory model (see the OpenSHMEM specification,
// api_mem_model.tex):
//
//   Step 1 - PEs and operation events:
//     * A memory location is now identified by (local address, PE id). We keep
//       the base `same_location` equivalence but require it to relate only
//       accesses that target the same PE, so each same_location class is a
//       distinct (addr, PE). This means the base coherence/mo/rf machinery,
//       which is phrased over `same_location`, is automatically per-(addr,PE).
//     * A new event type, `Operation`, represents an OpenSHMEM API call. It
//       participates in program order (sb) but not directly in mo/rf/sw.
//
//   Step 2 - Per-operation observable accesses:
//     * `issues` relates an Operation to the memory accesses it performs. These
//       observable accesses take part in mo/rf/sw with normal-access semantics,
//       EXCEPT that they have no program-order (po) relationship with the
//       initiating thread. Intra-operation ordering is captured by `op_sb`
//       (true data/control/ordering dependencies only), which is kept separate
//       from po.

open memory_consistency/llvm/events
open memory_consistency/llvm/memory
open memory_consistency/llvm/memory_ordering

open util/relation

// =============================================================================
// Step 1: PEs
// =============================================================================

// A processing element. Every OpenSHMEM PE has its own local memory space.
sig PE {
  // Accesses whose target memory resides on this PE. Declared on PE (rather
  // than as a field of Access) so we do not need to edit the base memory.als.
  target_of : set Access,

  // Events (operations, and accesses that live in a thread) whose issuing /
  // home PE is this one. This is the PE of the thread that executes the event,
  // as opposed to the PE whose memory an access targets.
  home_of : set Event,
}

// The PE whose memory an access targets.
fun target_pe : Access -> PE { ~target_of }

// The home (issuing) PE of an event.
fun home_pe : Event -> PE { ~home_of }

// Two accesses target the same PE.
fun same_pe : Access -> Access { ~target_of . target_of }

// =============================================================================
// Step 1: Operation events
// =============================================================================

// An OpenSHMEM API operation (put, get, atomic op, fence, quiet, barrier, ...).
// Operations are Events (so they take part in po/sb) but are neither Accesses
// nor Fences, so they never participate directly in mo/rf/sw.
sig Operation extends Event {
  // The observable memory accesses performed by this operation.
  issues : set Access,

  // Intra-operation ordering: (a, b) means observable access a is ordered
  // before observable access b by a true data/control/ordering dependency
  // within this operation. This is kept OUT of po (the base program order).
  op_sb : Access -> Access,
}

// All observable accesses across all operations.
fun observable_accesses : set Access { Operation.issues }

// The operation that issued a given observable access.
fun issued_by : Access -> Operation { ~issues }

// =============================================================================
// Operation classification (used by the API-level relations)
// =============================================================================
// These subset signatures classify operations by the categories the API model
// distinguishes. A concrete test/program assigns operations to these sets.

// Blocking operations are those without "nbi" in their name. NonBlocking is its
// complement within Operation.
sig NonBlocking in Operation {}

// Operation categories (from the observable-access table).
sig PutOp        in Operation {}   // shmem_put[_nbi], shmem_p, shmem_iput
sig GetOp        in Operation {}   // shmem_get[_nbi], shmem_g, shmem_iget
sig AmoOp        in Operation {}   // atomic memory operations
sig PutSignalOp  in Operation {}   // shmem_put_signal[_nbi]
sig SignalFetchOp in Operation {}  // shmem_signal_fetch
sig FenceOp      in Operation {}   // shmem_fence
// shmem_quiet. Carries quiet_order -- the quiet analog of memory_ordering's
// seqcst_order field: a total order over shmem_quiet operations, populated by
// api_quiet_sc (openshmem_predicates.als) to enforce quiet-based sequential
// consistency. Unconstrained unless that predicate is invoked.
sig QuietOp      in Operation {
  quiet_order : set QuietOp
}
sig BarrierOp    in Operation {}   // shmem_barrier_all, shmem_sync[_all]
sig P2PSyncOp    in Operation {}   // shmem_wait_until*, shmem_test*
sig LockOp       in Operation {}   // shmem_set/clear/test_lock

// Contexts with the OPENSHMEM_CTX_NOSTORE option enabled. Operations in this
// set have their outgoing store-side ordering (rdo/rco "unless NOSTORE" cases)
// suppressed.
sig NoStore in Operation {}

// Derived category groupings from the spec.

// fence-ordered operations: blocking or nonblocking put, atomic memory ops,
// put_signal.
fun fence_ordered_ops : set Operation { PutOp + AmoOp + PutSignalOp }

// qb-ordered operations: blocking or nonblocking put, nonblocking get, atomic
// memory ops, put_signal.
fun qb_ordered_ops : set Operation { PutOp + (GetOp & NonBlocking) + AmoOp + PutSignalOp }

// Operations whose observable reads/writes can participate in API
// synchronizes-with: atomic memory ops, signaling, p2p sync, locking.
fun asw_ops : set Operation { AmoOp + PutSignalOp + SignalFetchOp + P2PSyncOp + LockOp }

// Blocking operations: everything not marked NonBlocking.
fun blocking_ops : set Operation { Operation - NonBlocking }

// =============================================================================
// Structural facts
// =============================================================================

fact openshmem_pe_wellformed {
  // Every access targets exactly one PE.
  all a : Access | one a.target_pe

  // Same-location accesses must target the same PE (so each same_location class
  // is a distinct (addr, PE) pair).
  same_location in same_pe
}

fact openshmem_operation_wellformed {
  // Each observable access is issued by exactly one operation.
  all a : observable_accesses | one issues.a

  // Observable accesses are program-order-exempt: they have no po edge to or
  // from any event (in particular, none to the initiating thread).
  no observable_accesses <: po_imm
  no po_imm :> observable_accesses

  // op_sb only relates observable accesses of the SAME operation, and is
  // acyclic. It never coincides with po.
  all o : Operation | o.op_sb in (o.issues -> o.issues)
  acyclic[Operation.op_sb, Access]
  no (Operation.op_sb & po)

  // Operations themselves perform no memory accesses directly: an Operation is
  // not an Access or Fence (guaranteed by `extends`), and issues only real
  // Accesses.
}

fact openshmem_home_pe {
  // Every operation has a home PE (the PE of the calling thread).
  all o : Operation | one o.home_pe

  // Every access that lives in a thread (i.e. is not an observable access) has a
  // home PE: the PE of the thread that issues it.
  all a : Access - observable_accesses | one a.home_pe

  // A normal thread access may target a remote PE, e.g. a direct load/store
  // through a pointer obtained from shmem_ptr / shmem_team_ptr. Its home PE
  // remains the issuing thread's PE (fixed by the po grouping below), but its
  // target PE is unconstrained. Initialization writes, however, reside on the
  // PE they initialize (they are local writes).
  all i : Init | i.target_pe = i.home_pe

  // An observable access inherits the home PE of its issuing operation and has
  // no independent home PE assignment.
  no observable_accesses.home_pe

  // Program-order-connected events share a home PE (they run in one thread on
  // one PE).
  po in home_pe.~home_pe
}
