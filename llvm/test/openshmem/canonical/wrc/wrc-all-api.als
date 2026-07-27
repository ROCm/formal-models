module memory_consistency/llvm/test/openshmem/canonical/wrc/wrc_all_api

// Canonical WRC (write-to-read causality), realized entirely with API calls and
// synchronized with shmem_fence so causality propagates. FORBIDS the weak
// outcome, race-free.
//
// Classic WRC:
//   P0: x = 1
//   P1: r0 = x ; if (r0==1) y = 1
//   P2: r1 = y ; r2 = x
// Weak (forbidden): r0==1 && r1==1 && r2==0 (P2 sees y but not the causally
// prior x).
//
// OpenSHMEM realization (x, y hosted on PE3; a fence on P1 orders its read of x
// before its write of y, and a fence on P2 orders its read of y before its read
// of x):
//   PE0: shmem_atomic_set(x, 1, pe3)
//   PE1: r0 = shmem_atomic_fetch(x, pe3) ; shmem_fence() ; shmem_atomic_set(y, 1, pe3)
//   PE2: r1 = shmem_atomic_fetch(y, pe3) ; shmem_fence() ; r2 = shmem_atomic_fetch(x, pe3)
//
// Causal chain (closed entirely within api_hb):
//   st_x --asw--> ld_x1 --rdo--> st_y --asw--> ld_y2 --rdo--> ld_x2
// so once P2 observes y, its read of x must observe st_x (r2==0 forbidden).

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2, PE3 extends PE {}

one sig op_setx extends Operation {}                   // PE0
one sig op_fx1, op_fence1, op_sety extends Operation {} // PE1
one sig op_fy2, op_fence2, op_fx2 extends Operation {}  // PE2

one sig st_x  extends SimpleWrite {}   // atomic_set x@PE3 (P0)
one sig ld_x1 extends SimpleRead  {}   // atomic_fetch x@PE3 (P1)
one sig st_y  extends SimpleWrite {}   // atomic_set y@PE3 (P1)
one sig ld_y2 extends SimpleRead  {}   // atomic_fetch y@PE3 (P2)
one sig ld_x2 extends SimpleRead  {}   // atomic_fetch x@PE3 (P2)

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

// 1. The causal outcome is satisfiable and race-free: when P1 observes x and P2
//    observes y, P2's read of x observes st_x.
run causal_delivery {
  openshmem_memory_model
  (st_x -> ld_x1) in rf
  (st_y -> ld_y2) in rf
  (st_x -> ld_x2) in rf
  no_api_races
} for 0 but 16 Event expect 1

// 2. The weak outcome is FORBIDDEN: with the chain established, P2 cannot read
//    stale x (r2==0 impossible).
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
