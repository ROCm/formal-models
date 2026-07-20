module memory_consistency/llvm/openshmem_relations

// OpenSHMEM API-level memory model: base-independent additions (Steps 3 and 5).
//
// This module defines the OpenSHMEM API-level ordering relations
// (ilv/lco/rdo/rco/asw), api_hb, api_may_see, the shared happens-before /
// data-race consistency predicate, and the no-races convenience predicate.
//
// These pieces are independent of which flavor of the base memory-model axioms
// is used, so they are shared by both:
//   - openshmem_predicates_c11.als  (the spec's simplified C++/C11 axioms), and
//   - openshmem_predicates.als      (the repo's fuller LLVM axioms).
// Each of those modules adds the modification-order / coherence / seqcst axioms
// appropriate to its base and defines its own openshmem_memory_model.
//
// Fused collectives (Step 4) are represented structurally (see openshmem_model.als).

open memory_consistency/llvm/events
open memory_consistency/llvm/memory
open memory_consistency/llvm/memory_ordering
open memory_consistency/llvm/llvm_predicates
open memory_consistency/llvm/scopes
open memory_consistency/llvm/openshmem_events
open memory_consistency/llvm/utils

open util/relation

// The PL-level happens-before we build on. llvm_hb already includes program
// order, PL synchronizes-with (llvm_sw), and initialization ordering.
fun pl_hb : Event -> Event { llvm_hb }

// =============================================================================
// Step 3: API-level relations
// =============================================================================

// Implicit Local Visibility (ilv): a local observable access sees prior
// hb-ordered accesses from the initiating PE.
fun osh_ilv : Access -> Access {
  { A : Access, B : Access |
    B in observable_accesses and
    (let op = issued_by[B] |
       (A -> op) in pl_hb and
       B.target_pe = op.home_pe and     // B is a local observable access
       A.target_pe = op.home_pe)        // A targets the same (caller) PE
  }
}

// Local Completion Order (lco): a blocking operation completes its local
// observable accesses before subsequent hb-ordered events from the caller.
fun osh_lco : Access -> Event {
  { A : Access, B : Event |
    A in observable_accesses and
    (let op = issued_by[A] |
       op in blocking_ops and
       A.target_pe = op.home_pe and                              // A local
       ( (op -> B) in pl_hb or
         (B in observable_accesses and (op -> issued_by[B]) in pl_hb) ))
  }
}

// Remote Delivery Order (rdo): accesses separated by a shmem fence.
fun osh_rdo : Access -> Access {
  { A : Access, B : Access |
    B in observable_accesses and
    (some Fop : FenceOp |
       // case (i): A is a memory access hb-before the fence; B observable from
       // an op hb-after the fence; fence's context is not NOSTORE.
       ( (A -> Fop) in pl_hb and
         (Fop -> issued_by[B]) in pl_hb and
         Fop not in NoStore )
       or
       // case (ii): A observable from a fence-ordered op hb-before the fence; B
       // observable from an op hb-after the fence; A and B target the same PE.
       ( A in observable_accesses and
         issued_by[A] in fence_ordered_ops and
         (issued_by[A] -> Fop) in pl_hb and
         (Fop -> issued_by[B]) in pl_hb and
         A.target_pe = B.target_pe ))
  }
}

// Remote Completion Order (rco): full connectivity across a quiet or barrier.
fun osh_rco : Access -> Access {
  { A : Access, B : Access |
    some QB : (QuietOp + BarrierOp) |
      // case 1: thread access A hb-before QB, thread access B hb-after QB,
      // not NOSTORE.
      ( A not in observable_accesses and B not in observable_accesses and
        (A -> QB) in pl_hb and (QB -> B) in pl_hb and QB not in NoStore )
      or
      // case 2: thread access A hb-before QB, observable B hb-after QB,
      // not NOSTORE.
      ( A not in observable_accesses and B in observable_accesses and
        (A -> QB) in pl_hb and (QB -> issued_by[B]) in pl_hb and QB not in NoStore )
      or
      // case 3: observable A hb-before QB, any access B hb-after QB.
      ( A in observable_accesses and (issued_by[A] -> QB) in pl_hb and
        ( (B not in observable_accesses and (QB -> B) in pl_hb) or
          (B in observable_accesses and (QB -> issued_by[B]) in pl_hb) ) )
      or
      // case 4: observable A from a qb-ordered op hb-before QB, observable B
      // hb-after QB.
      ( A in observable_accesses and issued_by[A] in qb_ordered_ops and
        (issued_by[A] -> QB) in pl_hb and
        B in observable_accesses and (QB -> issued_by[B]) in pl_hb )
  }
}

// API Synchronizes-With (asw): the API analog of PL synchronizes-with. It
// relates an observable write/RMW to the observable read/RMW that reads from it,
// when both come from synchronizing operation categories. Direction follows the
// spec's worked example (store -> consuming load), i.e. write -> read, matching
// how PL sw is oriented (the definition's A/B labels are transposed; see report).
fun osh_asw : Write -> Read {
  { W : Write, R : Read |
    W in observable_accesses and R in observable_accesses and
    (W -> R) in rf and
    issued_by[W] in asw_ops and
    issued_by[R] in asw_ops }
}

// =============================================================================
// Step 5: api_hb, api_may_see, shared happens-before/data-race axiom
// =============================================================================

// API happens-before: transitive closure of PL hb, intra-operation dependency
// order, and all API-level relations.
fun api_hb : Event -> Event {
  ^(pl_hb + Operation.op_sb + osh_ilv + osh_lco + osh_rdo + osh_rco + osh_asw)
}

// Writes a Read may read from under api_hb without violating causality
// (analogous to llvm_may_see, but over api_hb and per-(addr,PE) same_location).
fun api_may_see : Write -> Read {
  (Write <: same_location :> Read) - (write_between[api_hb] + ~api_hb + iden)
}

// API happens-before consistency and API data races. This is the api_hb-
// retargeted analog of llvm_happens_before, shared by both base flavors.
pred api_happens_before {
  acyclic[api_hb, Event]

  rf in api_may_see

  // A Read is an (API) data race read iff it could read from >= 2 candidates
  // and at least one involved access is non-atomic (scopes are all compatible at
  // the API level, so the scope disjunct never fires here).
  all R : Read | R in DataRaceRead iff (
      let involved = R + api_may_see.R |
        (involved not in Atomic or (involved -> involved) not in compatible_scope)
          and (#api_may_see.R >= 2)
    )
}

// Convenience: no API data races.
pred no_api_races { no DataRaceRead }
