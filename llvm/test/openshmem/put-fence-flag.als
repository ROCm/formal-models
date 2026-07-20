module memory_consistency/llvm/test/openshmem/put_fence_flag

// Litmus test for the OpenSHMEM API-level memory model: the canonical
// message-passing idiom across two PEs.
//
//   PE0:  shmem_put(data, ...)      // writes data on PE1
//         shmem_fence()
//         shmem_atomic_set(flag, 1) // sets flag on PE1
//   PE1:  shmem_wait_until(flag==1) // spins on local flag
//         x = data                  // local read of data
//
// The API model must guarantee that PE1's read of data observes the value that
// PE0's put delivered, via the chain:
//   put.ST(data@PE1) --rdo--> set.ST(flag@PE1) --asw--> wait.LD(flag@PE1)
//     --lco--> PE1.load(data@PE1)
// so put.ST(data@PE1) api_hb-before PE1.load(data@PE1), forbidding the stale read.

open memory_consistency/llvm/openshmem_predicates_c11

// --- PEs ---
one sig PE0, PE1 extends PE {}

// --- Operations ---
one sig op_put   extends Operation {}   // PE0: blocking put
one sig op_fence extends Operation {}   // PE0: fence
one sig op_set   extends Operation {}   // PE0: atomic_set
one sig op_wait  extends Operation {}   // PE1: wait_until

// --- Observable accesses ---
one sig ld_src extends SimpleRead {}    // put: LD data@PE0 (local source)
one sig st_dst extends SimpleWrite {}   // put: ST data@PE1 (remote dest)
one sig st_flag extends SimpleWrite {}  // atomic_set: ST flag@PE1 (remote, atomic)
one sig ld_flag extends SimpleRead {}   // wait_until: LD flag@PE1 (local, atomic)

// --- Normal thread access ---
one sig load_data extends SimpleRead {} // PE1: local read of data@PE1

// --- Initialization writes (one per (addr, PE)) ---
one sig Init_data_pe0 extends Init {}
one sig Init_data_pe1 extends Init {}
one sig Init_flag_pe1 extends Init {}

fact program {
  // Program order within each thread (operations + the normal PE1 load).
  po_imm = op_put -> op_fence + op_fence -> op_set + op_wait -> load_data

  // Observable accesses issued by each operation (op_fence issues nothing).
  issues =
      op_put  -> ld_src + op_put -> st_dst +
      op_set  -> st_flag +
      op_wait -> ld_flag

  // Intra-operation dependency: the put stores the value it loaded.
  op_sb = op_put -> (ld_src -> st_dst)
  // (all other operations have empty op_sb)
  all o : Operation - op_put | no o.op_sb

  // Operation classification.
  PutOp        = op_put
  AmoOp        = op_set
  FenceOp      = op_fence
  P2PSyncOp    = op_wait
  no GetOp
  no PutSignalOp
  no SignalFetchOp
  no QuietOp
  no BarrierOp
  no LockOp
  no NonBlocking     // all operations here are blocking
  no NoStore
}

fact locations_and_pes {
  // Which PE each access targets (via PE.target_of).
  PE0.target_of = ld_src + Init_data_pe0
  PE1.target_of = st_dst + st_flag + ld_flag + load_data
                  + Init_data_pe1 + Init_flag_pe1

  // Home (issuing) PE of thread events (via PE.home_of). Observable accesses
  // have no home PE; Init writes are local so home = target.
  PE0.home_of = op_put + op_fence + op_set + Init_data_pe0
  PE1.home_of = op_wait + load_data + Init_data_pe1 + Init_flag_pe1

  // same_location equivalence classes = distinct (addr, PE) pairs.
  same_location =
      (Init_data_pe0 + ld_src) -> (Init_data_pe0 + ld_src) +
      (Init_data_pe1 + st_dst + load_data) -> (Init_data_pe1 + st_dst + load_data) +
      (Init_flag_pe1 + st_flag + ld_flag) -> (Init_flag_pe1 + st_flag + ld_flag)
}

fact atomicity {
  // The atomic_set store and the wait_until load are atomic (monotonic); the
  // put's data accesses and PE1's plain load are non-atomic.
  st_flag + ld_flag in Monotonic
  no (st_flag + ld_flag) & (Release + Acquire)
  no (ld_src + st_dst + load_data) & Atomic
}

fact scopes_flat {
  // Scopes are not exposed at the API level; put every non-Init event in the
  // System scope so the base scope constraints are trivially satisfied.
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// --- Checks ---

// 1. The intended (correct) execution exists and is race-free: PE1's wait
//    observes the flag, and PE1's load observes the put's data.
run good_outcome_exists {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf     // wait_until observes the set flag
  (st_dst -> load_data) in rf    // PE1's load observes the put
  no_api_races
} for 0 but 12 Event expect 1

// 2. Given the wait observes the flag, PE1's load CANNOT read the stale initial
//    value of data -- the API ordering forbids it. (unsat => ordering holds)
run stale_read_impossible {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  (Init_data_pe1 -> load_data) in rf
} for 0 but 12 Event expect 0

// 3. Control: if PE1's wait does NOT observe the flag (no API synchronization),
//    then PE1's plain read of data is unordered w.r.t. the put and is an API
//    data race. This confirms the ordering above is doing real work (the unsat
//    in check 2 is not vacuous).
run racy_without_sync {
  openshmem_memory_model
  (st_flag -> ld_flag) not in rf
  load_data in DataRaceRead
} for 0 but 12 Event expect 1
