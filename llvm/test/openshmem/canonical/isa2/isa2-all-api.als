module memory_consistency/llvm/test/openshmem/canonical/isa2/isa2_all_api

// Canonical ISA2 (transitive synchronization), realized entirely with API calls
// and synchronized with shmem_fence at each hop. FORBIDS the weak outcome,
// race-free.
//
// Classic ISA2:
//   P0: x = 1 ; release(a = 1)
//   P1: r0 = acquire(a) ; release(b = 1)
//   P2: r1 = acquire(b) ; r2 = x
// Weak (forbidden): r0==1 && r1==1 && r2==0 (P2 completes the a->b sync chain
// but does not see P0's causally prior write to x).
//
// OpenSHMEM realization (x, a, b all hosted on PE3; a fence on each PE orders the
// incoming access before the outgoing release, and orders P2's b-read before its
// x-read):
//   PE0: shmem_atomic_set(x, 1, pe3) ; shmem_fence() ; shmem_atomic_set(a, 1, pe3)
//   PE1: r0 = shmem_atomic_fetch(a, pe3) ; shmem_fence() ; shmem_atomic_set(b, 1, pe3)
//   PE2: r1 = shmem_atomic_fetch(b, pe3) ; shmem_fence() ; r2 = shmem_atomic_fetch(x, pe3)
//
// Transitive chain (closed entirely within api_hb):
//   st_x --rdo--> set_a --asw--> ld_a --rdo--> set_b --asw--> ld_b --rdo--> ld_x2
// so once P2 completes the chain it must observe st_x (r2==0 forbidden). This is
// WRC extended by one synchronization hop; it works because asw + rdo compose
// transitively.

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2, PE3 extends PE {}

one sig op_setx, op_f0, op_seta extends Operation {}   // PE0
one sig op_fa, op_f1, op_setb extends Operation {}      // PE1
one sig op_fb, op_f2, op_fx extends Operation {}        // PE2

one sig st_x  extends SimpleWrite {}   // atomic_set x@PE3 (P0)
one sig st_a  extends SimpleWrite {}   // atomic_set a@PE3 (P0, release)
one sig ld_a  extends SimpleRead  {}   // atomic_fetch a@PE3 (P1, acquire)
one sig st_b  extends SimpleWrite {}   // atomic_set b@PE3 (P1, release)
one sig ld_b  extends SimpleRead  {}   // atomic_fetch b@PE3 (P2, acquire)
one sig ld_x2 extends SimpleRead  {}   // atomic_fetch x@PE3 (P2)

one sig Init_x_pe3 extends Init {}
one sig Init_a_pe3 extends Init {}
one sig Init_b_pe3 extends Init {}

fact program {
  po_imm = op_setx -> op_f0 + op_f0 -> op_seta
         + op_fa -> op_f1 + op_f1 -> op_setb
         + op_fb -> op_f2 + op_f2 -> op_fx

  issues = op_setx -> st_x + op_seta -> st_a
         + op_fa -> ld_a + op_setb -> st_b
         + op_fb -> ld_b + op_fx -> ld_x2
  no op_sb

  AmoOp = op_setx + op_seta + op_fa + op_setb + op_fb + op_fx
  FenceOp = op_f0 + op_f1 + op_f2
  no PutOp and no GetOp
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

  PE0.home_of = op_setx + op_f0 + op_seta
  PE1.home_of = op_fa + op_f1 + op_setb
  PE2.home_of = op_fb + op_f2 + op_fx
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

// 1. The transitive delivery is satisfiable and race-free: P1 observes a, P2
//    observes b, and P2's read of x observes st_x.
run transitive_delivery {
  openshmem_memory_model
  (st_a -> ld_a) in rf
  (st_b -> ld_b) in rf
  (st_x -> ld_x2) in rf
  no_api_races
} for 0 but 20 Event expect 1

// 2. The weak outcome is FORBIDDEN: having completed the a->b chain, P2 cannot
//    read stale x (r2==0 impossible).
run weak_outcome_forbidden {
  openshmem_memory_model
  (st_a -> ld_a) in rf
  (st_b -> ld_b) in rf
  (Init_x_pe3 -> ld_x2) in rf
} for 0 but 20 Event expect 0

// 3. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 20 Event expect 0
