module memory_consistency/llvm/test/openshmem/canonical/sb/sb_all_api_relaxed

// Canonical SB (store buffering / Dekker), realized with REMOTE atomic accesses
// -- the OpenSHMEM analog of relaxed atomics. A remote atomic (target PE != home
// PE) is atomic (so no data race) but earns no ilv, no lco, and no rdo, so the
// store on each PE is NOT ordered before that PE's subsequent load. The classic
// weak SB outcome is therefore ALLOWED: race-free, but non-SC.
//
// Classic SB:  P0: x = 1 ; r0 = y      P1: y = 1 ; r1 = x
// Weak outcome (allowed here): r0 == 0 && r1 == 0 (each load sees the initial
// value, i.e. neither store is observed).
//
// OpenSHMEM realization (x and y both hosted on a third PE, PE2, so every shared
// access is remote):
//   PE0: shmem_atomic_set(x, 1, pe2)      // remote atomic ST x@PE2
//        r0 = shmem_atomic_fetch(y, pe2)  // remote atomic LD y@PE2
//   PE1: shmem_atomic_set(y, 1, pe2)      // remote atomic ST y@PE2
//        r1 = shmem_atomic_fetch(x, pe2)  // remote atomic LD x@PE2
//
// No ilv/lco/rdo (all accesses remote), no asw in the weak outcome (the loads
// read Init, not the stores). Nothing orders set-before-fetch on either PE.

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_set0, op_fetch0 extends Operation {}   // PE0
one sig op_set1, op_fetch1 extends Operation {}   // PE1

one sig st_x extends SimpleWrite {}   // atomic_set x@PE2 (remote atomic)
one sig ld_y extends SimpleRead  {}   // atomic_fetch y@PE2 (remote atomic)
one sig st_y extends SimpleWrite {}   // atomic_set y@PE2 (remote atomic)
one sig ld_x extends SimpleRead  {}   // atomic_fetch x@PE2 (remote atomic)

one sig Init_x_pe2 extends Init {}
one sig Init_y_pe2 extends Init {}

fact program {
  po_imm = op_set0 -> op_fetch0 + op_set1 -> op_fetch1

  issues = op_set0 -> st_x + op_fetch0 -> ld_y
         + op_set1 -> st_y + op_fetch1 -> ld_x
  no op_sb

  AmoOp = op_set0 + op_fetch0 + op_set1 + op_fetch1
  no PutOp and no GetOp and no FenceOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  no PE1.target_of
  PE2.target_of = st_x + ld_x + st_y + ld_y + Init_x_pe2 + Init_y_pe2

  PE0.home_of = op_set0 + op_fetch0
  PE1.home_of = op_set1 + op_fetch1
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

// 1. The weak SB outcome (both loads read the initial value) is ALLOWED and
//    race-free: remote atomics give no ordering between set and fetch.
run weak_outcome_allowed {
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
