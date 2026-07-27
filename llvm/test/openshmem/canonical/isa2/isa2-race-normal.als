module memory_consistency/llvm/test/openshmem/canonical/isa2/isa2_race_normal

// Canonical ISA2 with the accesses demoted to NORMAL (non-atomic) remote puts
// and gets. The flag accesses no longer synchronize (no asw), and the
// writer/reader pairs on x, a, and b are non-atomic and unsynchronized, so the
// execution has a DATA RACE. Relaxation counterpart of the race-free
// isa2-all-api.als.
//
//   PE0: shmem_put(x, ..., pe3) ; shmem_put(a, ..., pe3)
//   PE1: shmem_get(r0, a, pe3) ; shmem_put(b, ..., pe3)
//   PE2: shmem_get(r1, b, pe3) ; shmem_get(r2, x, pe3)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2, PE3 extends PE {}

one sig op_px, op_pa extends Operation {}   // PE0
one sig op_ga, op_pb extends Operation {}   // PE1
one sig op_gb, op_gx extends Operation {}   // PE2

one sig st_x  extends SimpleWrite {}   // put x@PE3 (P0)
one sig st_a  extends SimpleWrite {}   // put a@PE3 (P0)
one sig ld_a  extends SimpleRead  {}   // get a@PE3 (P1)
one sig st_b  extends SimpleWrite {}   // put b@PE3 (P1)
one sig ld_b  extends SimpleRead  {}   // get b@PE3 (P2)
one sig ld_x2 extends SimpleRead  {}   // get x@PE3 (P2)

one sig Init_x_pe3 extends Init {}
one sig Init_a_pe3 extends Init {}
one sig Init_b_pe3 extends Init {}

fact program {
  po_imm = op_px -> op_pa + op_ga -> op_pb + op_gb -> op_gx

  issues = op_px -> st_x + op_pa -> st_a
         + op_ga -> ld_a + op_pb -> st_b
         + op_gb -> ld_b + op_gx -> ld_x2
  no op_sb

  PutOp = op_px + op_pa + op_pb
  GetOp = op_ga + op_gb + op_gx
  no AmoOp and no FenceOp
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

  PE0.home_of = op_px + op_pa
  PE1.home_of = op_ga + op_pb
  PE2.home_of = op_gb + op_gx
  PE3.home_of = Init_x_pe3 + Init_a_pe3 + Init_b_pe3

  same_location =
      (Init_x_pe3 + st_x + ld_x2) -> (Init_x_pe3 + st_x + ld_x2) +
      (Init_a_pe3 + st_a + ld_a) -> (Init_a_pe3 + st_a + ld_a) +
      (Init_b_pe3 + st_b + ld_b) -> (Init_b_pe3 + st_b + ld_b)
}

fact atomicity {
  no (st_x + st_a + ld_a + st_b + ld_b + ld_x2) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. A data race is reachable (unsynchronized non-atomic put/get pairs).
run race_reachable {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 1

// 2. No race-free execution observes a write (any cross-PE delivery is a race).
run no_racefree_delivery {
  openshmem_memory_model
  (st_a -> ld_a) in rf
  no_api_races
} for 0 but 16 Event expect 0
