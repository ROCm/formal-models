module memory_consistency/llvm/test/openshmem/canonical/wrc/wrc_relaxed

// Canonical WRC with the fences REMOVED (remote atomics only). Without a fence
// on P1, its read of x is not ordered before its write of y, and without a fence
// on P2 its read of y is not ordered before its read of x. The causal chain is
// broken, so the weak outcome is ALLOWED (race-free, non-causal). Relaxation of
// wrc-all-api.als.
//
//   PE0: shmem_atomic_set(x, 1, pe3)
//   PE1: r0 = shmem_atomic_fetch(x, pe3) ; shmem_atomic_set(y, 1, pe3)
//   PE2: r1 = shmem_atomic_fetch(y, pe3) ; r2 = shmem_atomic_fetch(x, pe3)
//
// The observable accesses of distinct operations are program-order-exempt, so
// with no fence there is no ilv/lco/rdo edge from P1's read to P1's write (nor
// between P2's two reads). st_x --asw--> ld_x1 exists, but does not reach st_y.

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2, PE3 extends PE {}

one sig op_setx extends Operation {}         // PE0
one sig op_fx1, op_sety extends Operation {}  // PE1
one sig op_fy2, op_fx2 extends Operation {}   // PE2

one sig st_x  extends SimpleWrite {}
one sig ld_x1 extends SimpleRead  {}
one sig st_y  extends SimpleWrite {}
one sig ld_y2 extends SimpleRead  {}
one sig ld_x2 extends SimpleRead  {}

one sig Init_x_pe3 extends Init {}
one sig Init_y_pe3 extends Init {}

fact program {
  po_imm = op_fx1 -> op_sety + op_fy2 -> op_fx2

  issues = op_setx -> st_x
         + op_fx1 -> ld_x1 + op_sety -> st_y
         + op_fy2 -> ld_y2 + op_fx2 -> ld_x2
  no op_sb

  AmoOp = op_setx + op_fx1 + op_sety + op_fy2 + op_fx2
  no PutOp and no GetOp and no FenceOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  no PE1.target_of
  no PE2.target_of
  PE3.target_of = st_x + ld_x1 + ld_x2 + st_y + ld_y2
                + Init_x_pe3 + Init_y_pe3

  PE0.home_of = op_setx
  PE1.home_of = op_fx1 + op_sety
  PE2.home_of = op_fy2 + op_fx2
  PE3.home_of = Init_x_pe3 + Init_y_pe3

  same_location =
      (Init_x_pe3 + st_x + ld_x1 + ld_x2) -> (Init_x_pe3 + st_x + ld_x1 + ld_x2) +
      (Init_y_pe3 + st_y + ld_y2) -> (Init_y_pe3 + st_y + ld_y2)
}

fact atomicity {
  st_x + ld_x1 + st_y + ld_y2 + ld_x2 in Monotonic
  no (st_x + ld_x1 + st_y + ld_y2 + ld_x2) & (Release + Acquire)
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. The weak (non-causal) outcome is ALLOWED and race-free: no fence, so the
//    causal chain does not propagate x to P2's second read.
run weak_outcome_allowed {
  openshmem_memory_model
  (st_x -> ld_x1) in rf
  (st_y -> ld_y2) in rf
  (Init_x_pe3 -> ld_x2) in rf
  no_api_races
} for 0 but 16 Event expect 1

// 2. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
