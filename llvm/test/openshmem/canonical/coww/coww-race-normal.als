module memory_consistency/llvm/test/openshmem/canonical/coww/coww_race_normal

// Canonical CoWW with the accesses demoted to NORMAL (non-atomic) remote puts
// and gets. The writer's stores to x race with the observer's loads of x (same
// location, non-atomic, unsynchronized), so the execution has a DATA RACE.
// Relaxation counterpart of the race-free remote-atomic coww-all-api.als.
//
//   PE0: shmem_put(x, 1, pe2) ; shmem_fence() ; shmem_put(x, 2, pe2)
//   PE1: r0 = shmem_get(x, pe2) ; shmem_fence() ; r1 = shmem_get(x, pe2)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_w1, op_fw, op_w2 extends Operation {}   // PE0: put ; fence ; put
one sig op_ra, op_fr, op_rb extends Operation {}   // PE1: get ; fence ; get

one sig st1  extends SimpleWrite {}   // put x=1 (P0)
one sig st2  extends SimpleWrite {}   // put x=2 (P0)
one sig ld_a extends SimpleRead  {}   // get x (P1, first)
one sig ld_b extends SimpleRead  {}   // get x (P1, second)

one sig Init_x_pe2 extends Init {}

fact program {
  po_imm = op_w1 -> op_fw + op_fw -> op_w2
         + op_ra -> op_fr + op_fr -> op_rb

  issues = op_w1 -> st1 + op_w2 -> st2
         + op_ra -> ld_a + op_rb -> ld_b
  no op_sb

  PutOp = op_w1 + op_w2
  GetOp = op_ra + op_rb
  FenceOp = op_fw + op_fr
  no AmoOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  no PE1.target_of
  PE2.target_of = st1 + st2 + ld_a + ld_b + Init_x_pe2

  PE0.home_of = op_w1 + op_fw + op_w2
  PE1.home_of = op_ra + op_fr + op_rb
  PE2.home_of = Init_x_pe2

  same_location =
      (Init_x_pe2 + st1 + st2 + ld_a + ld_b) -> (Init_x_pe2 + st1 + st2 + ld_a + ld_b)
}

fact atomicity {
  no (st1 + st2 + ld_a + ld_b) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. A data race is reachable (unsynchronized non-atomic writer/reader on x).
run race_reachable {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 1

// 2. No race-free execution observes a written value (any delivery is a race).
run no_racefree_delivery {
  openshmem_memory_model
  (st1 -> ld_a) in rf
  no_api_races
} for 0 but 16 Event expect 0
