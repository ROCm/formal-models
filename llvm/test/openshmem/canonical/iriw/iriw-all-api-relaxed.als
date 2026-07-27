module memory_consistency/llvm/test/openshmem/canonical/iriw/iriw_all_api_relaxed

// Canonical IRIW (independent reads of independent writes), realized with REMOTE
// atomic accesses (the OpenSHMEM analog of relaxed atomics). Two observers read
// two independent writes in opposite orders. The weak outcome is ALLOWED here:
// remote atomics are not multi-copy atomic, so observers need not agree on a
// global order of independent writes. Race-free (all accesses atomic), non-SC.
//
// Classic IRIW:
//   P0: x = 1        P1: y = 1
//   P2: r0 = x ; r1 = y        P3: r2 = y ; r3 = x
// Weak outcome (allowed here): r0==1 && r1==0 && r2==1 && r3==0
//   (P2 sees x before y; P3 sees y before x).
//
// OpenSHMEM realization (x and y both hosted on PE4, so every access is remote):
//   PE0: shmem_atomic_set(x, 1, pe4)
//   PE1: shmem_atomic_set(y, 1, pe4)
//   PE2: r0 = shmem_atomic_fetch(x, pe4) ; r1 = shmem_atomic_fetch(y, pe4)
//   PE3: r2 = shmem_atomic_fetch(y, pe4) ; r3 = shmem_atomic_fetch(x, pe4)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2, PE3, PE4 extends PE {}

one sig op_setx  extends Operation {}                 // PE0
one sig op_sety  extends Operation {}                 // PE1
one sig op_fx2, op_fy2 extends Operation {}           // PE2
one sig op_fy3, op_fx3 extends Operation {}           // PE3

one sig st_x  extends SimpleWrite {}   // atomic_set x@PE4 (P0)
one sig st_y  extends SimpleWrite {}   // atomic_set y@PE4 (P1)
one sig ld_x2 extends SimpleRead  {}   // atomic_fetch x@PE4 (P2)
one sig ld_y2 extends SimpleRead  {}   // atomic_fetch y@PE4 (P2)
one sig ld_y3 extends SimpleRead  {}   // atomic_fetch y@PE4 (P3)
one sig ld_x3 extends SimpleRead  {}   // atomic_fetch x@PE4 (P3)

one sig Init_x_pe4 extends Init {}
one sig Init_y_pe4 extends Init {}

fact program {
  po_imm = op_fx2 -> op_fy2 + op_fy3 -> op_fx3

  issues = op_setx -> st_x + op_sety -> st_y
         + op_fx2 -> ld_x2 + op_fy2 -> ld_y2
         + op_fy3 -> ld_y3 + op_fx3 -> ld_x3
  no op_sb

  AmoOp = op_setx + op_sety + op_fx2 + op_fy2 + op_fy3 + op_fx3
  no PutOp and no GetOp and no FenceOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  no PE1.target_of
  no PE2.target_of
  no PE3.target_of
  PE4.target_of = st_x + ld_x2 + ld_x3 + st_y + ld_y2 + ld_y3
                + Init_x_pe4 + Init_y_pe4

  PE0.home_of = op_setx
  PE1.home_of = op_sety
  PE2.home_of = op_fx2 + op_fy2
  PE3.home_of = op_fy3 + op_fx3
  PE4.home_of = Init_x_pe4 + Init_y_pe4

  same_location =
      (Init_x_pe4 + st_x + ld_x2 + ld_x3) -> (Init_x_pe4 + st_x + ld_x2 + ld_x3) +
      (Init_y_pe4 + st_y + ld_y2 + ld_y3) -> (Init_y_pe4 + st_y + ld_y2 + ld_y3)
}

fact atomicity {
  st_x + st_y + ld_x2 + ld_y2 + ld_y3 + ld_x3 in Monotonic
  no (st_x + st_y + ld_x2 + ld_y2 + ld_y3 + ld_x3) & (Release + Acquire)
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. The weak IRIW outcome (observers disagree on the write order) is ALLOWED
//    and race-free: remote atomics are not multi-copy atomic.
run weak_outcome_allowed {
  openshmem_memory_model
  (st_x -> ld_x2) in rf         // P2: r0 = 1
  (Init_y_pe4 -> ld_y2) in rf   // P2: r1 = 0
  (st_y -> ld_y3) in rf         // P3: r2 = 1
  (Init_x_pe4 -> ld_x3) in rf   // P3: r3 = 0
  no_api_races
} for 0 but 16 Event expect 1

// 2. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
