module memory_consistency/llvm/test/openshmem/canonical/iriw/iriw_all_api_fence

// Canonical IRIW with a shmem_fence between each observer's two reads. FINDING:
// like SB, the fence is NOT sufficient to forbid the weak IRIW outcome -- it
// remains ALLOWED (race-free).
//
// The fence supplies rdo (case (ii), same host PE) ordering each observer's two
// loads (ld_x2 --rdo--> ld_y2 on PE2, ld_y3 --rdo--> ld_x3 on PE3), but
// forbidding IRIW requires multi-copy atomicity / a global SC order of the two
// independent writes -- a from-read cycle that is not part of api_hb. The spec's
// simplified C11 axioms omit SC, so no OpenSHMEM primitive restores multi-copy
// atomicity here. (Contrast WRC, whose causal chain IS closed by asw + rdo.)
//
//   PE0: shmem_atomic_set(x, 1, pe4)
//   PE1: shmem_atomic_set(y, 1, pe4)
//   PE2: shmem_atomic_fetch(x, pe4) ; shmem_fence() ; shmem_atomic_fetch(y, pe4)
//   PE3: shmem_atomic_fetch(y, pe4) ; shmem_fence() ; shmem_atomic_fetch(x, pe4)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2, PE3, PE4 extends PE {}

one sig op_setx  extends Operation {}                 // PE0
one sig op_sety  extends Operation {}                 // PE1
one sig op_fx2, op_fence2, op_fy2 extends Operation {} // PE2
one sig op_fy3, op_fence3, op_fx3 extends Operation {} // PE3

one sig st_x  extends SimpleWrite {}
one sig st_y  extends SimpleWrite {}
one sig ld_x2 extends SimpleRead  {}
one sig ld_y2 extends SimpleRead  {}
one sig ld_y3 extends SimpleRead  {}
one sig ld_x3 extends SimpleRead  {}

one sig Init_x_pe4 extends Init {}
one sig Init_y_pe4 extends Init {}

fact program {
  po_imm = op_fx2 -> op_fence2 + op_fence2 -> op_fy2
         + op_fy3 -> op_fence3 + op_fence3 -> op_fx3

  issues = op_setx -> st_x + op_sety -> st_y
         + op_fx2 -> ld_x2 + op_fy2 -> ld_y2
         + op_fy3 -> ld_y3 + op_fx3 -> ld_x3
  no op_sb

  AmoOp = op_setx + op_sety + op_fx2 + op_fy2 + op_fy3 + op_fx3
  FenceOp = op_fence2 + op_fence3
  no PutOp and no GetOp
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
  PE2.home_of = op_fx2 + op_fence2 + op_fy2
  PE3.home_of = op_fy3 + op_fence3 + op_fx3
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

// 1. Even with a fence on each observer, the weak IRIW outcome remains ALLOWED
//    and race-free (fence gives per-observer ordering, not multi-copy atomicity).
run weak_outcome_still_allowed {
  openshmem_memory_model
  (st_x -> ld_x2) in rf
  (Init_y_pe4 -> ld_y2) in rf
  (st_y -> ld_y3) in rf
  (Init_x_pe4 -> ld_x3) in rf
  no_api_races
} for 0 but 16 Event expect 1

// 2. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
