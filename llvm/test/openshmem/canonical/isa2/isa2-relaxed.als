module memory_consistency/llvm/test/openshmem/canonical/isa2/isa2_relaxed

// Canonical ISA2 with the fences REMOVED (remote atomics only). Without a fence
// on each PE, the incoming access is not ordered before the outgoing release
// (and P2's b-read is not ordered before its x-read), so the transitive chain
// does not carry x through. The weak outcome is ALLOWED (race-free, non-causal).
// Relaxation of isa2-all-api.als.
//
//   PE0: shmem_atomic_set(x, 1, pe3) ; shmem_atomic_set(a, 1, pe3)
//   PE1: r0 = shmem_atomic_fetch(a, pe3) ; shmem_atomic_set(b, 1, pe3)
//   PE2: r1 = shmem_atomic_fetch(b, pe3) ; r2 = shmem_atomic_fetch(x, pe3)
//
// The synchronizations set_a --asw--> ld_a and set_b --asw--> ld_b still exist,
// but with no rdo edges (no fences) they are not linked to st_x or to each other,
// so P2 can complete the a->b chain without observing x.

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2, PE3 extends PE {}

one sig op_setx, op_seta extends Operation {}   // PE0
one sig op_fa, op_setb extends Operation {}      // PE1
one sig op_fb, op_fx extends Operation {}        // PE2

one sig st_x  extends SimpleWrite {}
one sig st_a  extends SimpleWrite {}
one sig ld_a  extends SimpleRead  {}
one sig st_b  extends SimpleWrite {}
one sig ld_b  extends SimpleRead  {}
one sig ld_x2 extends SimpleRead  {}

one sig Init_x_pe3 extends Init {}
one sig Init_a_pe3 extends Init {}
one sig Init_b_pe3 extends Init {}

fact program {
  po_imm = op_setx -> op_seta + op_fa -> op_setb + op_fb -> op_fx

  issues = op_setx -> st_x + op_seta -> st_a
         + op_fa -> ld_a + op_setb -> st_b
         + op_fb -> ld_b + op_fx -> ld_x2
  no op_sb

  AmoOp = op_setx + op_seta + op_fa + op_setb + op_fb + op_fx
  no PutOp and no GetOp and no FenceOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  no PE1.target_of
  no PE2.target_of
  PE3.target_of = st_x + ld_x2 + st_a + ld_a + st_b + ld_b
                + Init_x_pe3 + Init_a_pe3 + Init_b_pe3

  PE0.home_of = op_setx + op_seta
  PE1.home_of = op_fa + op_setb
  PE2.home_of = op_fb + op_fx
  PE3.home_of = Init_x_pe3 + Init_a_pe3 + Init_b_pe3

  same_location =
      (Init_x_pe3 + st_x + ld_x2) -> (Init_x_pe3 + st_x + ld_x2) +
      (Init_a_pe3 + st_a + ld_a) -> (Init_a_pe3 + st_a + ld_a) +
      (Init_b_pe3 + st_b + ld_b) -> (Init_b_pe3 + st_b + ld_b)
}

fact atomicity {
  st_x + st_a + ld_a + st_b + ld_b + ld_x2 in Monotonic
  no (st_x + st_a + ld_a + st_b + ld_b + ld_x2) & (Release + Acquire)
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. The weak (non-causal) outcome is ALLOWED and race-free: with no fences the
//    chain does not propagate x, so P2 completes the a->b sync but reads stale x.
run weak_outcome_allowed {
  openshmem_memory_model
  (st_a -> ld_a) in rf
  (st_b -> ld_b) in rf
  (Init_x_pe3 -> ld_x2) in rf
  no_api_races
} for 0 but 16 Event expect 1

// 2. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
