module memory_consistency/llvm/test/openshmem/ilv_get_overwrites_local_store

// ilv test 2: a store to local memory followed by a get whose destination is
// the same (local) address. Implicit Local Visibility (ilv) must order the
// local store before the get's observable local store, so the get's store is
// later in modification order -- the final state of that memory reflects the
// get, not the overwritten local store. No data race.
//
//   PE0:  dest = 1                            // local store
//         shmem_get(dest, source@PE1, PE1)    // obs: LD source@PE1 ; ST dest@PE0
//
//   ilv: st_local(dest@PE0) --> st_get(dest@PE0)   [both local to caller PE0]
//   => mo must order st_local before st_get (the get wins); the reverse mo
//      order is forbidden by coherence over api_hb. This isolates ilv (no lco).

open memory_consistency/llvm/openshmem_predicates

one sig PE0, PE1 extends PE {}

one sig op_get extends Operation {}

one sig st_local extends SimpleWrite {}  // PE0: local store to dest@PE0
one sig ld_get   extends SimpleRead {}   // get: observable LD source@PE1 (remote)
one sig st_get   extends SimpleWrite {}  // get: observable ST dest@PE0 (local)

one sig Init_dest_pe0   extends Init {}
one sig Init_source_pe1 extends Init {}

fact program {
  po_imm = st_local -> op_get

  issues = op_get -> ld_get + op_get -> st_get
  op_sb  = op_get -> (ld_get -> st_get)

  GetOp = op_get
  no PutOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore     // blocking get
}

fact locations_and_pes {
  PE0.target_of = st_local + st_get + Init_dest_pe0
  PE1.target_of = ld_get + Init_source_pe1

  PE0.home_of = st_local + op_get + Init_dest_pe0
  PE1.home_of = Init_source_pe1

  same_location =
      (Init_dest_pe0 + st_local + st_get) -> (Init_dest_pe0 + st_local + st_get) +
      (Init_source_pe1 + ld_get) -> (Init_source_pe1 + ld_get)
}

fact atomicity {
  no (st_local + ld_get + st_get) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// The get's store is modification-ordered after the local store, race-free
// (the get overwrites the local store).
run get_store_after_local_store {
  openshmem_memory_model
  (st_local -> st_get) in mo
  no_api_races
} for 0 but 12 Event expect 1

// The local store cannot be modification-ordered after the get's store: ilv
// puts st_local api_hb-before st_get, and mo must be consistent with api_hb, so
// the get's store always wins.
run local_store_cannot_win {
  openshmem_memory_model
  (st_get -> st_local) in mo
} for 0 but 12 Event expect 0
