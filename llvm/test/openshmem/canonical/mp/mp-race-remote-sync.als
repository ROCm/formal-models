module memory_consistency/llvm/test/openshmem/canonical/mp/mp_race_remote_sync

// Canonical MP, race-inducing (API-only) via REMOTE synchronizing READ (removes
// lco). Same as mp-all-api, but the flag lives on a third PE (PE2) and the
// consumer observes it with a REMOTE atomic_fetch instead of a local wait_until.
// lco (which carried the ordering to the consumer's get) is local-only, so the
// remote fetch does not order the subsequent get -> the get's read of x races
// with the put. Racing pair homogeneous (both API).
//
//   PE0: shmem_put(x, xsrc, pe1)          // LD xsrc@PE0 ; ST x@PE1
//        shmem_fence()
//        shmem_atomic_set(flag, 1, pe2)   // ST flag@PE2 (atomic)
//   PE1: r0 = shmem_atomic_fetch(flag, pe2) // LD flag@PE2 (atomic, REMOTE)
//        shmem_get(r, x, pe1)             // LD x@PE1 ; ST r@PE1 (local self-get)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_put, op_fence, op_set extends Operation {}   // PE0
one sig op_fetch, op_rget extends Operation {}          // PE1

one sig ld_xsrc extends SimpleRead {}
one sig st_x    extends SimpleWrite {}
one sig st_flag extends SimpleWrite {}   // atomic_set: ST flag@PE2 (atomic)
one sig ld_flag extends SimpleRead {}    // atomic_fetch: LD flag@PE2 (atomic, REMOTE)
one sig ld_x    extends SimpleRead {}
one sig st_r    extends SimpleWrite {}

one sig Init_xsrc_pe0 extends Init {}
one sig Init_x_pe1    extends Init {}
one sig Init_flag_pe2 extends Init {}
one sig Init_r_pe1    extends Init {}

fact program {
  po_imm = op_put -> op_fence + op_fence -> op_set + op_fetch -> op_rget

  issues = op_put -> ld_xsrc + op_put -> st_x
         + op_set -> st_flag
         + op_fetch -> ld_flag
         + op_rget -> ld_x + op_rget -> st_r
  op_sb  = op_put -> (ld_xsrc -> st_x) + op_rget -> (ld_x -> st_r)

  PutOp = op_put
  FenceOp = op_fence
  AmoOp = op_set + op_fetch        // atomic_set and atomic_fetch are AMOs
  GetOp = op_rget
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = ld_xsrc + Init_xsrc_pe0
  PE1.target_of = st_x + ld_x + st_r + Init_x_pe1 + Init_r_pe1
  PE2.target_of = st_flag + ld_flag + Init_flag_pe2

  PE0.home_of = op_put + op_fence + op_set + Init_xsrc_pe0
  PE1.home_of = op_fetch + op_rget + Init_x_pe1 + Init_r_pe1
  PE2.home_of = Init_flag_pe2

  same_location =
      (Init_xsrc_pe0 + ld_xsrc) -> (Init_xsrc_pe0 + ld_xsrc) +
      (Init_x_pe1 + st_x + ld_x) -> (Init_x_pe1 + st_x + ld_x) +
      (Init_flag_pe2 + st_flag + ld_flag) -> (Init_flag_pe2 + st_flag + ld_flag) +
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

// 1. Even with the flag observed via the remote fetch, the get's read of x races.
run race_on_x {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  ld_x in DataRaceRead
} for 0 but 16 Event expect 1

// 2. No race-free execution delivers the put's x to the get (remote fetch -> no lco).
run no_racefree_delivery {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) in rf
  no_api_races
} for 0 but 16 Event expect 0
