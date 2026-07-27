module memory_consistency/llvm/test/openshmem/canonical/sb/sb_all_api_fence

// Canonical SB with a shmem_fence inserted between each PE's atomic_set and
// atomic_fetch. FINDING: the fence is NOT sufficient to forbid the weak SB
// outcome -- it remains ALLOWED (race-free).
//
// Why: forbidding SB requires closing a from-read cycle
//   st_x --order--> ld_y --fr--> st_y --order--> ld_x --fr--> st_x,
// which needs a *store->load* (sequentially consistent) fence. OpenSHMEM's
// shmem_fence provides only remote-delivery (release/acquire-style) ordering:
// it contributes rdo edges (st_x --rdo--> ld_y, st_y --rdo--> ld_x when the
// locations share a host PE), but rdo only adds api_hb edges. The model checks
// acyclic(api_hb); the from-read edges are not part of api_hb, and the spec's
// simplified C11 axioms omit SC entirely. So no OpenSHMEM primitive (fence,
// quiet, or barrier) restores SC for SB in this model.
//
// Contrast: LB *is* restored by a fence (see ../lb/lb-all-api-sc.als) because
// its forbidding cycle is closed by asw (rf) + rdo, both already in api_hb.
//
//   PE0: shmem_atomic_set(x, 1, pe2) ; shmem_fence() ; shmem_atomic_fetch(y, pe2)
//   PE1: shmem_atomic_set(y, 1, pe2) ; shmem_fence() ; shmem_atomic_fetch(x, pe2)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_set0, op_fence0, op_fetch0 extends Operation {}   // PE0
one sig op_set1, op_fence1, op_fetch1 extends Operation {}   // PE1

one sig st_x extends SimpleWrite {}
one sig ld_y extends SimpleRead  {}
one sig st_y extends SimpleWrite {}
one sig ld_x extends SimpleRead  {}

one sig Init_x_pe2 extends Init {}
one sig Init_y_pe2 extends Init {}

fact program {
  po_imm = op_set0 -> op_fence0 + op_fence0 -> op_fetch0
         + op_set1 -> op_fence1 + op_fence1 -> op_fetch1

  issues = op_set0 -> st_x + op_fetch0 -> ld_y
         + op_set1 -> st_y + op_fetch1 -> ld_x
  no op_sb

  AmoOp = op_set0 + op_fetch0 + op_set1 + op_fetch1
  FenceOp = op_fence0 + op_fence1
  no PutOp and no GetOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  no PE1.target_of
  PE2.target_of = st_x + ld_x + st_y + ld_y + Init_x_pe2 + Init_y_pe2

  PE0.home_of = op_set0 + op_fence0 + op_fetch0
  PE1.home_of = op_set1 + op_fence1 + op_fetch1
  PE2.home_of = Init_x_pe2 + Init_y_pe2

  same_location =
      (Init_x_pe2 + st_x + ld_x) -> (Init_x_pe2 + st_x + ld_x) +
      (Init_y_pe2 + st_y + ld_y) -> (Init_y_pe2 + st_y + ld_y)
}

fact atomicity {
  st_x + ld_x + st_y + ld_y in Monotonic
  no (st_x + ld_x + st_y + ld_y) & (Release + Acquire)
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. Even with a fence on each PE, the weak SB outcome remains ALLOWED and
//    race-free (fence gives delivery ordering, not SC store->load ordering).
run weak_outcome_still_allowed {
  openshmem_memory_model
  (Init_x_pe2 -> ld_x) in rf
  (Init_y_pe2 -> ld_y) in rf
  no_api_races
} for 0 but 16 Event expect 1

// 2. Every execution is race-free (all shared accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
