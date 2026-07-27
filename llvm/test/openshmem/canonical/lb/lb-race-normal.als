module memory_consistency/llvm/test/openshmem/canonical/lb/lb_race_normal

// Canonical LB with the atomics demoted to NORMAL (non-atomic) remote accesses:
// a remote get for each load and a remote put for each store. The cross accesses
// to x (PE0 reads, PE1 writes) and to y (PE1 reads, PE0 writes) are non-atomic
// and unsynchronized, so the execution has a DATA RACE. Relaxation counterpart
// of the race-free remote-atomic LB in lb-all-api-relaxed.als.
//
//   PE0: shmem_get(r0, x, pe2)   // normal LD x@PE2 ; ST r0@PE0
//        shmem_put(y, ..., pe2)  // normal ST y@PE2
//   PE1: shmem_get(r1, y, pe2)   // normal LD y@PE2 ; ST r1@PE1
//        shmem_put(x, ..., pe2)  // normal ST x@PE2

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_get0, op_put0 extends Operation {}   // PE0
one sig op_get1, op_put1 extends Operation {}   // PE1

one sig ld_x extends SimpleRead  {}   // get: LD x@PE2 (P0)
one sig st_r0 extends SimpleWrite {}  // get: ST r0@PE0 (local result)
one sig st_y extends SimpleWrite {}   // put: ST y@PE2 (P0)
one sig ld_y extends SimpleRead  {}   // get: LD y@PE2 (P1)
one sig st_r1 extends SimpleWrite {}  // get: ST r1@PE1 (local result)
one sig st_x extends SimpleWrite {}   // put: ST x@PE2 (P1)

one sig Init_x_pe2 extends Init {}
one sig Init_y_pe2 extends Init {}
one sig Init_r0_pe0 extends Init {}
one sig Init_r1_pe1 extends Init {}

fact program {
  po_imm = op_get0 -> op_put0 + op_get1 -> op_put1

  issues = op_get0 -> ld_x + op_get0 -> st_r0 + op_put0 -> st_y
         + op_get1 -> ld_y + op_get1 -> st_r1 + op_put1 -> st_x
  op_sb = op_get0 -> (ld_x -> st_r0) + op_get1 -> (ld_y -> st_r1)

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
  PE2.target_of = ld_x + st_x + ld_y + st_y + Init_x_pe2 + Init_y_pe2

  PE0.home_of = op_get0 + op_put0 + Init_r0_pe0
  PE1.home_of = op_get1 + op_put1 + Init_r1_pe1
  PE2.home_of = Init_x_pe2 + Init_y_pe2

  same_location =
      (Init_x_pe2 + st_x + ld_x) -> (Init_x_pe2 + st_x + ld_x) +
      (Init_y_pe2 + st_y + ld_y) -> (Init_y_pe2 + st_y + ld_y) +
      (Init_r0_pe0 + st_r0) -> (Init_r0_pe0 + st_r0) +
      (Init_r1_pe1 + st_r1) -> (Init_r1_pe1 + st_r1)
}

fact atomicity {
  no (ld_x + st_r0 + st_y + ld_y + st_r1 + st_x) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. A data race is reachable (unsynchronized non-atomic cross accesses).
run race_reachable {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 1

// 2. No race-free execution observes a store across PEs.
run no_racefree_cross_delivery {
  openshmem_memory_model
  (st_x -> ld_x) in rf
  no_api_races
} for 0 but 16 Event expect 0
