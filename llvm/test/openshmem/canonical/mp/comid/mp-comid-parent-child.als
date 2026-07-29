module memory_consistency/llvm/test/openshmem/canonical/mp/comid/mp_comid_parent_child

// MP with com_id, COMPARABLE (ancestor/descendant) case. The producer is tagged
// with a child com_id C_lo and the consumer with its parent C_hi (C_hi is an
// ancestor of C_lo; both under the global com_id). Their com_ids are COMPARABLE,
// so under the revised gate -- where condition (2) constrains only non-observable
// access endpoints -- the asw bridge st_flag [C_lo] -> ld_flag [C_hi] is
// established at c = C_lo (both synchronizing ops are >= C_lo), and the full
// rdo/asw/lco chain forms at c = C_lo. Result: race-free and SC, just like the
// single-com_id match.
//
//   PE0: shmem_put(x, xsrc, pe1)   [C_lo] ; fence [C_lo] ; atomic_set(flag,1,pe1) [C_lo]
//   PE1: shmem_wait_until(flag==1) [C_hi] ; shmem_get(r, x, pe1) [C_hi]
//
// Note: under the earlier gate (which also constrained observable endpoints <= c)
// asw would have required C_lo = C_hi exactly, so this would have raced. It is SC
// only because observable endpoints are now exempt from condition (2).

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

// --- com_id: producer in child C_lo, consumer in ancestor C_hi ---
one sig C_hi, C_lo extends ComId {}
fact comids {
  C_hi.com_parent = GlobalComId
  C_lo.com_parent = C_hi
  C_lo.tagged = op_put + op_fence + op_set   // producer (child scope)
  C_hi.tagged = op_wait + op_rget            // consumer (parent scope)
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
} for 0 but 16 Event, exactly 3 ComId expect 1

// 2. SC retained across comparable com_ids: the get cannot read stale x.
run cannot_read_stale_x {
  openshmem_comid_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) not in rf
} for 0 but 16 Event, exactly 3 ComId expect 0

// 3. No data race in any legal execution where the flag is observed.
run no_data_race {
  openshmem_comid_memory_model
  (st_flag -> ld_flag) in rf
  not no_api_races_comid
} for 0 but 16 Event, exactly 3 ComId expect 0
