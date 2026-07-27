module memory_consistency/llvm/test/openshmem/canonical/iriw/iriw_race_normal

// Canonical IRIW with the atomics demoted to NORMAL (non-atomic) remote
// accesses: remote puts for the writes, remote gets for the reads. Each writer
// races with the observers reading the same location, and the accesses are
// non-atomic, so the execution has a DATA RACE. Relaxation counterpart of the
// race-free remote-atomic IRIW in iriw-all-api-relaxed.als.
//
//   PE0: shmem_put(x, ..., pe4)                      // normal ST x@PE4
//   PE1: shmem_put(y, ..., pe4)                      // normal ST y@PE4
//   PE2: shmem_get(r0, x, pe4) ; shmem_get(r1, y, pe4)
//   PE3: shmem_get(r2, y, pe4) ; shmem_get(r3, x, pe4)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2, PE3, PE4 extends PE {}

one sig op_px  extends Operation {}                 // PE0
one sig op_py  extends Operation {}                 // PE1
one sig op_gx2, op_gy2 extends Operation {}         // PE2
one sig op_gy3, op_gx3 extends Operation {}         // PE3

one sig st_x  extends SimpleWrite {}   // put x@PE4 (P0)
one sig st_y  extends SimpleWrite {}   // put y@PE4 (P1)
one sig ld_x2 extends SimpleRead  {}   // get x@PE4 (P2)
one sig st_r0 extends SimpleWrite {}   // get result r0@PE2
one sig ld_y2 extends SimpleRead  {}   // get y@PE4 (P2)
one sig st_r1 extends SimpleWrite {}   // get result r1@PE2
one sig ld_y3 extends SimpleRead  {}   // get y@PE4 (P3)
one sig st_r2 extends SimpleWrite {}   // get result r2@PE3
one sig ld_x3 extends SimpleRead  {}   // get x@PE4 (P3)
one sig st_r3 extends SimpleWrite {}   // get result r3@PE3

one sig Init_x_pe4 extends Init {}
one sig Init_y_pe4 extends Init {}
one sig Init_r0_pe2 extends Init {}
one sig Init_r1_pe2 extends Init {}
one sig Init_r2_pe3 extends Init {}
one sig Init_r3_pe3 extends Init {}

fact program {
  po_imm = op_gx2 -> op_gy2 + op_gy3 -> op_gx3

  issues = op_px -> st_x + op_py -> st_y
         + op_gx2 -> ld_x2 + op_gx2 -> st_r0
         + op_gy2 -> ld_y2 + op_gy2 -> st_r1
         + op_gy3 -> ld_y3 + op_gy3 -> st_r2
         + op_gx3 -> ld_x3 + op_gx3 -> st_r3
  op_sb = op_gx2 -> (ld_x2 -> st_r0) + op_gy2 -> (ld_y2 -> st_r1)
        + op_gy3 -> (ld_y3 -> st_r2) + op_gx3 -> (ld_x3 -> st_r3)

  PutOp = op_px + op_py
  GetOp = op_gx2 + op_gy2 + op_gy3 + op_gx3
  no AmoOp and no FenceOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  no PE1.target_of
  PE2.target_of = st_r0 + st_r1 + Init_r0_pe2 + Init_r1_pe2
  PE3.target_of = st_r2 + st_r3 + Init_r2_pe3 + Init_r3_pe3
  PE4.target_of = st_x + ld_x2 + ld_x3 + st_y + ld_y2 + ld_y3
                + Init_x_pe4 + Init_y_pe4

  PE0.home_of = op_px
  PE1.home_of = op_py
  PE2.home_of = op_gx2 + op_gy2 + Init_r0_pe2 + Init_r1_pe2
  PE3.home_of = op_gy3 + op_gx3 + Init_r2_pe3 + Init_r3_pe3
  PE4.home_of = Init_x_pe4 + Init_y_pe4

  same_location =
      (Init_x_pe4 + st_x + ld_x2 + ld_x3) -> (Init_x_pe4 + st_x + ld_x2 + ld_x3) +
      (Init_y_pe4 + st_y + ld_y2 + ld_y3) -> (Init_y_pe4 + st_y + ld_y2 + ld_y3) +
      (Init_r0_pe2 + st_r0) -> (Init_r0_pe2 + st_r0) +
      (Init_r1_pe2 + st_r1) -> (Init_r1_pe2 + st_r1) +
      (Init_r2_pe3 + st_r2) -> (Init_r2_pe3 + st_r2) +
      (Init_r3_pe3 + st_r3) -> (Init_r3_pe3 + st_r3)
}

fact atomicity {
  no (st_x + st_y + ld_x2 + ld_y2 + ld_y3 + ld_x3
      + st_r0 + st_r1 + st_r2 + st_r3) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. A data race is reachable (unsynchronized non-atomic writer/reader pairs).
run race_reachable {
  openshmem_memory_model
  not no_api_races
} for 0 but 20 Event expect 1

// 2. No race-free execution observes a write (any cross-PE delivery is a race).
run no_racefree_delivery {
  openshmem_memory_model
  (st_x -> ld_x2) in rf
  no_api_races
} for 0 but 20 Event expect 0
