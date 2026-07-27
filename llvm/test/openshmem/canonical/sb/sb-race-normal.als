module memory_consistency/llvm/test/openshmem/canonical/sb/sb_race_normal

// Canonical SB with the atomics demoted to NORMAL (non-atomic) remote accesses:
// a remote put for each store and a remote get for each load. Nothing
// synchronizes the concurrent accesses to x (PE0's store vs PE1's load) or to y
// (PE1's store vs PE0's load), and the accesses are non-atomic, so the execution
// has a DATA RACE. This is the relaxation counterpart of the race-free
// remote-atomic SB in sb-all-api-relaxed.als.
//
//   PE0: shmem_put(x, ..., pe2)   // normal ST x@PE2
//        shmem_get(r0, y, pe2)    // normal LD y@PE2 ; ST r0@PE0
//   PE1: shmem_put(y, ..., pe2)   // normal ST y@PE2
//        shmem_get(r1, x, pe2)    // normal LD x@PE2 ; ST r1@PE1

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_put0, op_get0 extends Operation {}   // PE0
one sig op_put1, op_get1 extends Operation {}   // PE1

one sig st_x extends SimpleWrite {}   // put: ST x@PE2 (normal)
one sig ld_y extends SimpleRead  {}   // get: LD y@PE2 (normal)
one sig st_r0 extends SimpleWrite {}  // get: ST r0@PE0 (local result)
one sig st_y extends SimpleWrite {}   // put: ST y@PE2 (normal)
one sig ld_x extends SimpleRead  {}   // get: LD x@PE2 (normal)
one sig st_r1 extends SimpleWrite {}  // get: ST r1@PE1 (local result)

one sig Init_x_pe2 extends Init {}
one sig Init_y_pe2 extends Init {}
one sig Init_r0_pe0 extends Init {}
one sig Init_r1_pe1 extends Init {}

fact program {
  po_imm = op_put0 -> op_get0 + op_put1 -> op_get1

  issues = op_put0 -> st_x + op_get0 -> ld_y + op_get0 -> st_r0
         + op_put1 -> st_y + op_get1 -> ld_x + op_get1 -> st_r1
  op_sb = op_get0 -> (ld_y -> st_r0) + op_get1 -> (ld_x -> st_r1)

  PutOp = op_put0 + op_put1
  GetOp = op_get0 + op_get1
  no AmoOp and no FenceOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = st_r0 + Init_r0_pe0
  PE1.target_of = st_r1 + Init_r1_pe1
  PE2.target_of = st_x + ld_x + st_y + ld_y + Init_x_pe2 + Init_y_pe2

  PE0.home_of = op_put0 + op_get0 + Init_r0_pe0
  PE1.home_of = op_put1 + op_get1 + Init_r1_pe1
  PE2.home_of = Init_x_pe2 + Init_y_pe2

  same_location =
      (Init_x_pe2 + st_x + ld_x) -> (Init_x_pe2 + st_x + ld_x) +
      (Init_y_pe2 + st_y + ld_y) -> (Init_y_pe2 + st_y + ld_y) +
      (Init_r0_pe0 + st_r0) -> (Init_r0_pe0 + st_r0) +
      (Init_r1_pe1 + st_r1) -> (Init_r1_pe1 + st_r1)
}

fact atomicity {
  no (st_x + ld_y + st_r0 + st_y + ld_x + st_r1) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. A data race is reachable: e.g. PE1's get reads PE0's store of x with no
//    synchronization between them.
run race_reachable {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 1

// 2. There is no race-free execution that observes a store across PEs (the
//    normal accesses are unordered, so any cross-PE delivery is a race).
run no_racefree_cross_delivery {
  openshmem_memory_model
  (st_x -> ld_x) in rf
  no_api_races
} for 0 but 16 Event expect 0
