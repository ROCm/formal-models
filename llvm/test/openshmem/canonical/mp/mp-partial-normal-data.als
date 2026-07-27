module memory_consistency/llvm/test/openshmem/canonical/mp/mp_partial_normal_data

// Canonical MP, partial API version: the DATA accesses are normal (a direct
// remote store on the producer via shmem_ptr, and a local load on the consumer),
// while the SYNCHRONIZING accesses remain API. The racing data pair is
// homogeneous (both normal). Race-free.
//
//   PE0: *ptr_to_PE1_x = 1                 // normal ST x@PE1 (remote, shmem_ptr)
//        shmem_fence()
//        shmem_atomic_set(flag, 1, pe1)    // ST flag@PE1 (atomic)
//   PE1: shmem_wait_until(flag == 1)       // LD flag@PE1 (atomic, local)
//        r1 = x                            // normal LD x@PE1

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_fence, op_set extends Operation {}   // PE0
one sig op_wait extends Operation {}            // PE1

one sig st_x    extends SimpleWrite {}  // PE0: normal remote store to x@PE1
one sig st_flag extends SimpleWrite {}  // atomic_set: ST flag@PE1 (atomic)
one sig ld_flag extends SimpleRead {}   // wait_until: LD flag@PE1 (atomic, local)
one sig ld_x    extends SimpleRead {}   // PE1: normal local load of x@PE1

one sig Init_x_pe1    extends Init {}
one sig Init_flag_pe1 extends Init {}

fact program {
  po_imm = st_x -> op_fence + op_fence -> op_set + op_wait -> ld_x

  issues = op_set -> st_flag + op_wait -> ld_flag
  no op_sb

  FenceOp = op_fence
  AmoOp = op_set
  P2PSyncOp = op_wait
  no PutOp and no GetOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  PE1.target_of = st_x + st_flag + ld_flag + ld_x + Init_x_pe1 + Init_flag_pe1

  PE0.home_of = st_x + op_fence + op_set
  PE1.home_of = op_wait + ld_x + Init_x_pe1 + Init_flag_pe1

  same_location =
      (Init_x_pe1 + st_x + ld_x) -> (Init_x_pe1 + st_x + ld_x) +
      (Init_flag_pe1 + st_flag + ld_flag) -> (Init_flag_pe1 + st_flag + ld_flag)
}

fact atomicity {
  st_flag + ld_flag in Monotonic
  no (st_flag + ld_flag) & (Release + Acquire)
  no (st_x + ld_x) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

run can_read_put {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) in rf
  no_api_races
} for 0 but 12 Event expect 1

run cannot_read_stale_x {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) not in rf
} for 0 but 12 Event expect 0

run no_data_race {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  not no_api_races
} for 0 but 12 Event expect 0
