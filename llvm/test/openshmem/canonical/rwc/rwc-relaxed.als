module memory_consistency/llvm/test/openshmem/canonical/rwc/rwc_relaxed

// Canonical RWC (read-to-write causality), realized with REMOTE atomic accesses
// and NO fence. The star of the RWC family: even though P1 reads x (observing 1)
// and THEN writes y in program order, that read-to-write pair carries no
// ordering -- observable accesses of distinct operations are program-order-
// exempt and OpenSHMEM has no dependency-ordering relation. So the weak outcome
// is ALLOWED (race-free, non-causal).
//
// Classic RWC:
//   P0: x = 1
//   P1: r0 = x ; y = 1            (no dependency: y=1 is plain program order)
//   P2: r1 = y ; r2 = x
// Weak (allowed here): r0==1 && r1==1 && r2==0.
//
//   PE0: shmem_atomic_set(x, 1, pe3)
//   PE1: r0 = shmem_atomic_fetch(x, pe3) ; shmem_atomic_set(y, 1, pe3)
//   PE2: r1 = shmem_atomic_fetch(y, pe3) ; r2 = shmem_atomic_fetch(x, pe3)
//
// To forbid the weak outcome, an explicit fence is required on P1 (and P2); see
// rwc-all-api.als. Unlike WRC there is no value dependency to fall back on -- but
// in this model that makes no difference, since dependencies are not tracked as
// ordering for observable accesses either way.

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

// 1. The weak outcome is ALLOWED and race-free: a program-order read-then-write
//    carries no ordering without a fence.
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
