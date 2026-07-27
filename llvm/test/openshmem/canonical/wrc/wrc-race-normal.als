module memory_consistency/llvm/test/openshmem/canonical/wrc/wrc_race_normal

// Canonical WRC with the accesses demoted to NORMAL (non-atomic) remote puts and
// gets. The writer/reader pairs on x (P0 put vs P1 get) and y (P1 put vs P2 get)
// are non-atomic and unsynchronized, so the execution has a DATA RACE.
// Relaxation counterpart of the race-free wrc-all-api.als.
//
//   PE0: shmem_put(x, ..., pe3)
//   PE1: shmem_get(r0, x, pe3) ; shmem_put(y, ..., pe3)
//   PE2: shmem_get(r1, y, pe3) ; shmem_get(r2, x, pe3)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2, PE3 extends PE {}

one sig op_px extends Operation {}          // PE0
one sig op_gx1, op_py extends Operation {}   // PE1
one sig op_gy2, op_gx2 extends Operation {}  // PE2

one sig st_x  extends SimpleWrite {}   // put x@PE3 (P0)
one sig ld_x1 extends SimpleRead  {}   // get x@PE3 (P1)
one sig st_y  extends SimpleWrite {}   // put y@PE3 (P1)
one sig ld_y2 extends SimpleRead  {}   // get y@PE3 (P2)
one sig ld_x2 extends SimpleRead  {}   // get x@PE3 (P2)

one sig Init_x_pe3 extends Init {}
one sig Init_y_pe3 extends Init {}

fact program {
  po_imm = op_gx1 -> op_py + op_gy2 -> op_gx2

  issues = op_px -> st_x
         + op_gx1 -> ld_x1 + op_py -> st_y
         + op_gy2 -> ld_y2 + op_gx2 -> ld_x2
  no op_sb

  PutOp = op_px + op_py
  GetOp = op_gx1 + op_gy2 + op_gx2
  no AmoOp and no FenceOp
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

  PE0.home_of = op_px
  PE1.home_of = op_gx1 + op_py
  PE2.home_of = op_gy2 + op_gx2
  PE3.home_of = Init_x_pe3 + Init_y_pe3

  same_location =
      (Init_x_pe3 + st_x + ld_x1 + ld_x2) -> (Init_x_pe3 + st_x + ld_x1 + ld_x2) +
      (Init_y_pe3 + st_y + ld_y2) -> (Init_y_pe3 + st_y + ld_y2)
}

fact atomicity {
  no (st_x + ld_x1 + st_y + ld_y2 + ld_x2) & Atomic
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
  (st_x -> ld_x1) in rf
  no_api_races
} for 0 but 16 Event expect 0
