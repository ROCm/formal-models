module memory_consistency/llvm/test/openshmem/canonical/lb/lb_all_api_sc

// Canonical LB made SC by inserting a shmem_fence between each PE's atomic_fetch
// and atomic_set. Compare lb-all-api-relaxed.als (no fence -> weak allowed).
//
// Unlike SB (which needs a store->load SC fence that OpenSHMEM lacks), LB is
// restored by a plain shmem_fence: the fence supplies rdo (case (ii), same host
// PE) ordering the load before the following store on each PE
//   ld_x0 --rdo--> st_y0        ld_y1 --rdo--> st_x1
// and the weak outcome's cross reads give asw (rf) edges
//   st_y0 --asw--> ld_y1        st_x1 --asw--> ld_x0.
// Together these close a cycle entirely within api_hb:
//   ld_x0 --rdo--> st_y0 --asw--> ld_y1 --rdo--> st_x1 --asw--> ld_x0,
// which acyclic(api_hb) forbids. So the weak LB outcome is FORBIDDEN.
//
//   PE0: r0 = shmem_atomic_fetch(x, pe2) ; shmem_fence() ; shmem_atomic_set(y, 1, pe2)
//   PE1: r1 = shmem_atomic_fetch(y, pe2) ; shmem_fence() ; shmem_atomic_set(x, 1, pe2)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_fetch0, op_fence0, op_set0 extends Operation {}   // PE0
one sig op_fetch1, op_fence1, op_set1 extends Operation {}   // PE1

one sig ld_x extends SimpleRead  {}
one sig st_y extends SimpleWrite {}
one sig ld_y extends SimpleRead  {}
one sig st_x extends SimpleWrite {}

one sig Init_x_pe2 extends Init {}
one sig Init_y_pe2 extends Init {}

fact program {
  po_imm = op_fetch0 -> op_fence0 + op_fence0 -> op_set0
         + op_fetch1 -> op_fence1 + op_fence1 -> op_set1

  issues = op_fetch0 -> ld_x + op_set0 -> st_y
         + op_fetch1 -> ld_y + op_set1 -> st_x
  no op_sb

  AmoOp = op_fetch0 + op_set0 + op_fetch1 + op_set1
  FenceOp = op_fence0 + op_fence1
  no PutOp and no GetOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  no PE1.target_of
  PE2.target_of = ld_x + st_x + ld_y + st_y + Init_x_pe2 + Init_y_pe2

  PE0.home_of = op_fetch0 + op_fence0 + op_set0
  PE1.home_of = op_fetch1 + op_fence1 + op_set1
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

// 1. Some legal, race-free execution exists (model is consistent).
run some_execution {
  openshmem_memory_model
  no_api_races
} for 0 but 16 Event expect 1

// 2. The weak LB outcome is FORBIDDEN: fences supply rdo (load->store), and the
//    cross reads supply asw, closing an api_hb cycle.
run weak_outcome_forbidden {
  openshmem_memory_model
  (st_x -> ld_x) in rf
  (st_y -> ld_y) in rf
} for 0 but 16 Event expect 0

// 3. Every execution is race-free (all shared accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
