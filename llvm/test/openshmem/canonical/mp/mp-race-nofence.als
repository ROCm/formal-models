module memory_consistency/llvm/test/openshmem/canonical/mp/mp_race_nofence

// Canonical MP, race-inducing (API-only) via FENCE REMOVAL. Same as mp-all-api
// but with the fence between the put and the atomic_set removed. Without the
// fence there is no rdo edge, so the put's delivery of x is not ordered before
// the flag, and the consumer's get of x races with the put. The racing pair is
// homogeneous (both API observable accesses to x@PE1).
//
//   PE0: shmem_put(x, xsrc, pe1)          // LD xsrc@PE0 ; ST x@PE1   [NO FENCE]
//        shmem_atomic_set(flag, 1, pe1)   // ST flag@PE1 (atomic)
//   PE1: shmem_wait_until(flag == 1)      // LD flag@PE1 (atomic, local)
//        shmem_get(r, x, pe1)             // LD x@PE1 ; ST r@PE1 (local self-get)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_put, op_set extends Operation {}   // PE0 (no fence)
one sig op_wait, op_rget extends Operation {} // PE1

one sig ld_xsrc extends SimpleRead {}
one sig st_x    extends SimpleWrite {}
one sig st_flag extends SimpleWrite {}
one sig ld_flag extends SimpleRead {}
one sig ld_x    extends SimpleRead {}
one sig st_r    extends SimpleWrite {}

one sig Init_xsrc_pe0 extends Init {}
one sig Init_x_pe1    extends Init {}
one sig Init_flag_pe1 extends Init {}
one sig Init_r_pe1    extends Init {}

fact program {
  po_imm = op_put -> op_set + op_wait -> op_rget

  issues = op_put -> ld_xsrc + op_put -> st_x
         + op_set -> st_flag
         + op_wait -> ld_flag
         + op_rget -> ld_x + op_rget -> st_r
  op_sb  = op_put -> (ld_xsrc -> st_x) + op_rget -> (ld_x -> st_r)

  PutOp = op_put
  AmoOp = op_set
  P2PSyncOp = op_wait
  GetOp = op_rget
  no FenceOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = ld_xsrc + Init_xsrc_pe0
  PE1.target_of = st_x + st_flag + ld_flag + ld_x + st_r
                  + Init_x_pe1 + Init_flag_pe1 + Init_r_pe1

  PE0.home_of = op_put + op_set + Init_xsrc_pe0
  PE1.home_of = op_wait + op_rget + Init_x_pe1 + Init_flag_pe1 + Init_r_pe1

  same_location =
      (Init_xsrc_pe0 + ld_xsrc) -> (Init_xsrc_pe0 + ld_xsrc) +
      (Init_x_pe1 + st_x + ld_x) -> (Init_x_pe1 + st_x + ld_x) +
      (Init_flag_pe1 + st_flag + ld_flag) -> (Init_flag_pe1 + st_flag + ld_flag) +
      (Init_r_pe1 + st_r) -> (Init_r_pe1 + st_r)
}

fact atomicity {
  st_flag + ld_flag in Monotonic
  no (st_flag + ld_flag) & (Release + Acquire)
  no (ld_xsrc + st_x + ld_x + st_r) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. Even with the flag observed, the get's read of x races with the put.
run race_on_x {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  ld_x in DataRaceRead
} for 0 but 16 Event expect 1

// 2. No race-free execution delivers the put's x to the get (no fence -> no rdo).
run no_racefree_delivery {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) in rf
  no_api_races
} for 0 but 16 Event expect 0
