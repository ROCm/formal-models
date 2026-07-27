module memory_consistency/llvm/test/openshmem/canonical/rwc/rwc_all_api

// Canonical RWC synchronized with shmem_fence so the read-to-write and
// read-to-read orderings hold. FORBIDS the weak outcome, race-free.
//
// A fence on P1 orders its read of x before its write of y (rdo case (ii), same
// host PE), and a fence on P2 orders its read of y before its read of x. The
// resulting chain is closed entirely within api_hb:
//   st_x --asw--> ld_x1 --rdo--> st_y --asw--> ld_y2 --rdo--> ld_x2
// so once P2 observes y it must observe st_x (r2==0 forbidden).
//
// In this model RWC and WRC coincide once synchronized: OpenSHMEM tracks no
// dependency ordering for observable accesses, so both rely on the fence to
// order P1's read before its write. (WRC's value dependency buys nothing extra
// here.)
//
//   PE0: shmem_atomic_set(x, 1, pe3)
//   PE1: r0 = shmem_atomic_fetch(x, pe3) ; shmem_fence() ; shmem_atomic_set(y, 1, pe3)
//   PE2: r1 = shmem_atomic_fetch(y, pe3) ; shmem_fence() ; r2 = shmem_atomic_fetch(x, pe3)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2, PE3 extends PE {}

one sig op_setx extends Operation {}                   // PE0
one sig op_fx1, op_fence1, op_sety extends Operation {} // PE1
one sig op_fy2, op_fence2, op_fx2 extends Operation {}  // PE2

one sig st_x  extends SimpleWrite {}
one sig ld_x1 extends SimpleRead  {}
one sig st_y  extends SimpleWrite {}
one sig ld_y2 extends SimpleRead  {}
one sig ld_x2 extends SimpleRead  {}

one sig Init_x_pe3 extends Init {}
one sig Init_y_pe3 extends Init {}

fact program {
  po_imm = op_fx1 -> op_fence1 + op_fence1 -> op_sety
         + op_fy2 -> op_fence2 + op_fence2 -> op_fx2

  issues = op_setx -> st_x
         + op_fx1 -> ld_x1 + op_sety -> st_y
         + op_fy2 -> ld_y2 + op_fx2 -> ld_x2
  no op_sb

  AmoOp = op_setx + op_fx1 + op_sety + op_fy2 + op_fx2
  FenceOp = op_fence1 + op_fence2
  no PutOp and no GetOp
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
  PE1.home_of = op_fx1 + op_fence1 + op_sety
  PE2.home_of = op_fy2 + op_fence2 + op_fx2
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

// 1. The causal outcome is satisfiable and race-free.
run causal_delivery {
  openshmem_memory_model
  (st_x -> ld_x1) in rf
  (st_y -> ld_y2) in rf
  (st_x -> ld_x2) in rf
  no_api_races
} for 0 but 16 Event expect 1

// 2. The weak outcome is FORBIDDEN: with the fences in place P2 cannot read
//    stale x once it observes y.
run weak_outcome_forbidden {
  openshmem_memory_model
  (st_x -> ld_x1) in rf
  (st_y -> ld_y2) in rf
  (Init_x_pe3 -> ld_x2) in rf
} for 0 but 16 Event expect 0

// 3. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
