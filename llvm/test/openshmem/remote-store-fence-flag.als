module memory_consistency/llvm/test/openshmem/remote_store_fence_flag

// Litmus test exercising a NORMAL (non-observable) access that targets a REMOTE
// PE -- e.g. a direct store through a pointer obtained from shmem_ptr /
// shmem_team_ptr. This is the message-passing idiom, but PE0 delivers the
// payload with a direct remote store instead of shmem_put:
//
//   PE0:  *ptr_to_PE1_data = 1      // NORMAL store, home=PE0, target=PE1
//         shmem_fence()
//         shmem_atomic_set(flag, 1) // sets flag on PE1
//   PE1:  shmem_wait_until(flag==1)
//         x = data                  // local read of data@PE1
//
// The remote normal store is ordered before PE1's read via:
//   st_rem(data@PE1) --rdo(i)--> set.ST(flag@PE1) --asw--> wait.LD(flag@PE1)
//     --lco--> load(data@PE1)
// Note st_rem is a normal thread access (in program order), yet targets PE1,
// which the relaxed model now permits and rdo case (i) consumes.

open memory_consistency/llvm/openshmem_predicates_c11

// --- PEs ---
one sig PE0, PE1 extends PE {}

// --- Operations (PE0: fence, atomic_set; PE1: wait_until) ---
one sig op_fence extends Operation {}
one sig op_set   extends Operation {}
one sig op_wait  extends Operation {}

// --- Observable accesses of the atomic_set / wait_until ---
one sig st_flag extends SimpleWrite {}  // atomic_set: ST flag@PE1 (atomic)
one sig ld_flag extends SimpleRead {}   // wait_until: LD flag@PE1 (atomic)

// --- Normal thread accesses ---
one sig st_rem    extends SimpleWrite {} // PE0: direct remote store to data@PE1
one sig load_data extends SimpleRead {}  // PE1: local read of data@PE1

// --- Initialization writes (one per (addr, PE)) ---
one sig Init_data_pe1 extends Init {}
one sig Init_flag_pe1 extends Init {}

fact program {
  // Program order: the remote store is an ordinary in-thread access on PE0.
  po_imm = st_rem -> op_fence + op_fence -> op_set + op_wait -> load_data

  issues = op_set -> st_flag + op_wait -> ld_flag

  // no intra-operation dependencies here
  no op_sb

  PutOp        = none
  AmoOp        = op_set
  FenceOp      = op_fence
  P2PSyncOp    = op_wait
  no GetOp
  no PutSignalOp
  no SignalFetchOp
  no QuietOp
  no BarrierOp
  no LockOp
  no NonBlocking
  no NoStore
}

fact locations_and_pes {
  // No access targets PE0's memory; everything here lives on PE1.
  no PE0.target_of
  PE1.target_of = st_rem + st_flag + ld_flag + load_data
                  + Init_data_pe1 + Init_flag_pe1

  // Home (issuing) PE. st_rem is issued by a PE0 thread but targets PE1 (remote).
  PE0.home_of = st_rem + op_fence + op_set
  PE1.home_of = op_wait + load_data + Init_data_pe1 + Init_flag_pe1

  // same_location classes = distinct (addr, PE) pairs (all on PE1 here).
  same_location =
      (Init_data_pe1 + st_rem + load_data) -> (Init_data_pe1 + st_rem + load_data) +
      (Init_flag_pe1 + st_flag + ld_flag) -> (Init_flag_pe1 + st_flag + ld_flag)
}

fact atomicity {
  st_flag + ld_flag in Monotonic
  no (st_flag + ld_flag) & (Release + Acquire)
  no (st_rem + load_data) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// --- Checks ---

// 0. Sanity: the model admits a normal access that targets a remote PE
//    (st_rem home=PE0, target=PE1). Under the old local-only constraint this
//    was unsatisfiable.
run remote_normal_access_ok {
  openshmem_memory_model
  st_rem in PE1.target_of        // targets a remote PE ...
  st_rem in PE0.home_of          // ... while issued from PE0
} for 0 but 10 Event expect 1

// 1. The intended race-free execution exists.
run good_outcome_exists {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  (st_rem -> load_data) in rf
  no_api_races
} for 0 but 10 Event expect 1

// 2. Given synchronization, PE1's load cannot read the stale initial value:
//    the remote normal store is api_hb-ordered before it (via rdo -> asw -> lco).
run stale_read_impossible {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  (Init_data_pe1 -> load_data) in rf
} for 0 but 10 Event expect 0

// 3. Control: without synchronization, the remote store and the local read race.
run racy_without_sync {
  openshmem_memory_model
  (st_flag -> ld_flag) not in rf
  load_data in DataRaceRead
} for 0 but 10 Event expect 1
