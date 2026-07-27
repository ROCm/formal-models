module memory_consistency/llvm/test/openshmem/canonical/lb/lb_all_api_relaxed

// Canonical LB (load buffering), realized with REMOTE atomic accesses -- the
// OpenSHMEM analog of relaxed atomics. Remote atomics earn no ilv/lco/rdo, so
// the load on each PE is not ordered before that PE's subsequent store. The
// weak LB outcome is therefore ALLOWED: race-free, but non-SC.
//
// Classic LB:  P0: r0 = x ; y = 1      P1: r1 = y ; x = 1
// Weak outcome (allowed here): r0 == 1 && r1 == 1 (each load reads the other
// PE's later store).
//
// OpenSHMEM realization (x and y both hosted on PE2, so every shared access is
// remote):
//   PE0: r0 = shmem_atomic_fetch(x, pe2)  // remote atomic LD x@PE2
//        shmem_atomic_set(y, 1, pe2)      // remote atomic ST y@PE2
//   PE1: r1 = shmem_atomic_fetch(y, pe2)  // remote atomic LD y@PE2
//        shmem_atomic_set(x, 1, pe2)      // remote atomic ST x@PE2
//
// In the weak outcome the loads read the cross stores, giving asw edges
// (st_x1 --asw--> ld_x0, st_y0 --asw--> ld_y1), but with no fence there is no
// rdo edge from a load to the following store, so no api_hb cycle forms.

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_fetch0, op_set0 extends Operation {}   // PE0
one sig op_fetch1, op_set1 extends Operation {}   // PE1

one sig ld_x extends SimpleRead  {}   // atomic_fetch x@PE2 (P0)
one sig st_y extends SimpleWrite {}   // atomic_set   y@PE2 (P0)
one sig ld_y extends SimpleRead  {}   // atomic_fetch y@PE2 (P1)
one sig st_x extends SimpleWrite {}   // atomic_set   x@PE2 (P1)

one sig Init_x_pe2 extends Init {}
one sig Init_y_pe2 extends Init {}

fact program {
  po_imm = op_fetch0 -> op_set0 + op_fetch1 -> op_set1

  issues = op_fetch0 -> ld_x + op_set0 -> st_y
         + op_fetch1 -> ld_y + op_set1 -> st_x
  no op_sb

  AmoOp = op_fetch0 + op_set0 + op_fetch1 + op_set1
  no PutOp and no GetOp and no FenceOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  no PE1.target_of
  PE2.target_of = ld_x + st_x + ld_y + st_y + Init_x_pe2 + Init_y_pe2

  PE0.home_of = op_fetch0 + op_set0
  PE1.home_of = op_fetch1 + op_set1
  PE2.home_of = Init_x_pe2 + Init_y_pe2

  same_location =
      (Init_x_pe2 + st_x + ld_x) -> (Init_x_pe2 + st_x + ld_x) +
      (Init_y_pe2 + st_y + ld_y) -> (Init_y_pe2 + st_y + ld_y)
}

fact atomicity {
  ld_x + st_x + ld_y + st_y in Monotonic
  no (ld_x + st_x + ld_y + st_y) & (Release + Acquire)
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. The weak LB outcome (each load reads the other PE's store) is ALLOWED and
//    race-free: remote atomics give no load->store ordering.
run weak_outcome_allowed {
  openshmem_memory_model
  (st_x -> ld_x) in rf
  (st_y -> ld_y) in rf
  no_api_races
} for 0 but 16 Event expect 1

// 2. Every execution is race-free (all shared accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
