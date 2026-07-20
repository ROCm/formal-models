module memory_consistency/llvm/test/openshmem/ilv_get_overwrites_local_store

// ilv test 2: a store to local memory followed by a get whose destination is
// the same (local) address. Implicit Local Visibility (ilv) must order the
// local store before the get's observable local store, so the final state of
// that memory reflects the get, not the overwritten local store. No data race.
//
//   PE0:  dest = 1                            // local store
//         shmem_get(dest, source@PE1, PE1)    // obs: LD source@PE1 ; ST dest@PE0
//         x = dest                            // local read observes the final state
//
//   ilv: st_local(dest@PE0) --> st_get(dest@PE0)     [both local to caller PE0]
//   lco: st_get(dest@PE0)   --> ld_final(dest@PE0)   [blocking get completes locally]
//
// This uses a downstream local read (ld_final) rather than a modification-order
// direction check, so ordering is established via api_hb (write_between), not mo.
// That makes the test flavor-independent: it runs under both the C11-based and
// the LLVM-based OpenSHMEM predicates (the LLVM model restricts mo to atomic
// writes, so an mo-based version would only work under the C11 model).

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_get extends Operation {}

one sig st_local extends SimpleWrite {}  // PE0: local store to dest@PE0
one sig ld_get   extends SimpleRead {}   // get: observable LD source@PE1 (remote)
one sig st_get   extends SimpleWrite {}  // get: observable ST dest@PE0 (local)
one sig ld_final extends SimpleRead {}   // PE0: local read of dest@PE0 after the get

one sig Init_dest_pe0   extends Init {}
one sig Init_source_pe1 extends Init {}

fact program {
  po_imm = st_local -> op_get + op_get -> ld_final

  issues = op_get -> ld_get + op_get -> st_get
  op_sb  = op_get -> (ld_get -> st_get)

  GetOp = op_get
  no PutOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore     // blocking get
}

fact locations_and_pes {
  PE0.target_of = st_local + st_get + ld_final + Init_dest_pe0
  PE1.target_of = ld_get + Init_source_pe1

  PE0.home_of = st_local + op_get + ld_final + Init_dest_pe0
  PE1.home_of = Init_source_pe1

  same_location =
      (Init_dest_pe0 + st_local + st_get + ld_final)
        -> (Init_dest_pe0 + st_local + st_get + ld_final) +
      (Init_source_pe1 + ld_get) -> (Init_source_pe1 + ld_get)
}

fact atomicity {
  no (st_local + ld_get + st_get + ld_final) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// The final local read observes the get's store, race-free.
run final_state_is_get {
  openshmem_memory_model
  (st_get -> ld_final) in rf
  no_api_races
} for 0 but 14 Event expect 1

// The final local read cannot observe the overwritten local store (ilv orders
// the local store before the get's store, and lco orders the get's store before
// the read, so the get wins).
run final_state_not_store {
  openshmem_memory_model
  (st_local -> ld_final) in rf
} for 0 but 14 Event expect 0
