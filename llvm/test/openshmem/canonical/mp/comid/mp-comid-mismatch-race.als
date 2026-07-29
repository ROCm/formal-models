module memory_consistency/llvm/test/openshmem/canonical/mp/comid/mp_comid_mismatch_race

// MP with com_id, MISMATCHING case: the producer and the consumer use two
// DIFFERENT com_ids (C_prod and C_cons) that are incomparable siblings under the
// global com_id. API synchronizes-with (asw) requires the flag's writer op and
// reader op to share a com_id (the gate forces the relation-com_id c to equal
// both), so the flag write st_flag [C_prod] does NOT synchronize with the flag
// read ld_flag [C_cons]. The rdo/lco links still form within each PE, but the
// cross-PE asw bridge is missing, so nothing orders the put's store of x before
// the get's read of x -> DATA RACE on x (even though the flag itself is atomic).
//
//   PE0: shmem_put(x, xsrc, pe1)   [C_prod] ; fence [C_prod] ; atomic_set(flag,1,pe1) [C_prod]
//   PE1: shmem_wait_until(flag==1) [C_cons] ; shmem_get(r, x, pe1) [C_cons]
//
// Compare mp-comid-match.als (all one com_id -> race-free, SC).

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

// --- com_id: producer and consumer in incomparable sibling com_ids ---
one sig C_prod, C_cons extends ComId {}
fact comids {
  C_prod.com_parent = GlobalComId
  C_cons.com_parent = GlobalComId
  C_prod.tagged = op_put + op_fence + op_set   // producer
  C_cons.tagged = op_wait + op_rget            // consumer
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

// 1. Even when the flag is observed, the get's read of x is a data-race read:
//    the com_id mismatch removes the asw bridge, so x is not ordered.
run race_on_x {
  openshmem_comid_memory_model
  (st_flag -> ld_flag) in rf
  ld_x in DataRaceRead
} for 0 but 16 Event, exactly 3 ComId expect 1

// 2. No race-free execution delivers the put's x to the get.
run no_racefree_delivery {
  openshmem_comid_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) in rf
  no_api_races_comid
} for 0 but 16 Event, exactly 3 ComId expect 0
