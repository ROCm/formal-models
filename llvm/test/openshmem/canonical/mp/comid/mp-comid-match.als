module memory_consistency/llvm/test/openshmem/canonical/mp/comid/mp_comid_match

// MP with com_id, MATCHING case: every operation (and hence every observable
// access) carries the SAME com_id C1 (a child of the global com_id). With all
// com_ids equal, the whole rdo/asw/lco chain is established at c = C1, so the
// behavior is identical to the plain all-API MP (../mp-all-api.als): race-free
// and SC (the get cannot read stale x). This shows com_id support recovers the
// original behavior when com_ids agree.
//
//   PE0: shmem_put(x, xsrc, pe1)   [C1] ; shmem_fence() [C1] ; shmem_atomic_set(flag,1,pe1) [C1]
//   PE1: shmem_wait_until(flag==1) [C1] ; shmem_get(r, x, pe1) [C1]

open memory_consistency/llvm/openshmem_comid

one sig PE0, PE1 extends PE {}

one sig op_put, op_fence, op_set extends Operation {}   // PE0
one sig op_wait, op_rget extends Operation {}           // PE1

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

// --- com_id: one non-global id C1 tagging every operation (accesses inherit) ---
one sig C1 extends ComId {}
fact comids {
  C1.com_parent = GlobalComId
  C1.tagged = op_put + op_fence + op_set + op_wait + op_rget
  no GlobalComId.tagged
}

fact program {
  po_imm = op_put -> op_fence + op_fence -> op_set + op_wait -> op_rget

  issues = op_put -> ld_xsrc + op_put -> st_x
         + op_set -> st_flag
         + op_wait -> ld_flag
         + op_rget -> ld_x + op_rget -> st_r
  op_sb  = op_put -> (ld_xsrc -> st_x) + op_rget -> (ld_x -> st_r)

  PutOp = op_put
  FenceOp = op_fence
  AmoOp = op_set
  P2PSyncOp = op_wait
  GetOp = op_rget
  no PutSignalOp and no SignalFetchOp and no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = ld_xsrc + Init_xsrc_pe0
  PE1.target_of = st_x + st_flag + ld_flag + ld_x + st_r
                  + Init_x_pe1 + Init_flag_pe1 + Init_r_pe1

  PE0.home_of = op_put + op_fence + op_set + Init_xsrc_pe0
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

// 1. Expected behavior is satisfiable: the get reads the put's x, race-free.
run can_read_put {
  openshmem_comid_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) in rf
  no_api_races_comid
} for 0 but 16 Event, exactly 2 ComId expect 1

// 2. SC retained: given the flag is observed, the get cannot read stale x.
run cannot_read_stale_x {
  openshmem_comid_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) not in rf
} for 0 but 16 Event, exactly 2 ComId expect 0

// 3. No data race in any legal execution where the flag is observed.
run no_data_race {
  openshmem_comid_memory_model
  (st_flag -> ld_flag) in rf
  not no_api_races_comid
} for 0 but 16 Event, exactly 2 ComId expect 0
