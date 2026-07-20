module memory_consistency/llvm/test/openshmem/ilv_local_load_before_get_store

// ilv test 3: a load from local memory followed by a get whose destination is
// the same (local) address. Implicit Local Visibility (ilv) must order the
// local load before the get's observable local store, so the load cannot read
// the value the get delivers. No data race.
//
//   PE0:  x = dest                            // local load
//         shmem_get(dest, source@PE1, PE1)    // obs: LD source@PE1 ; ST dest@PE0
//
//   ilv: ld_local(dest@PE0) --> st_get(dest@PE0)   [both local to caller PE0]

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_get extends Operation {}

one sig ld_local extends SimpleRead {}   // PE0: local load of dest@PE0
one sig ld_get   extends SimpleRead {}   // get: observable LD source@PE1 (remote)
one sig st_get   extends SimpleWrite {}  // get: observable ST dest@PE0 (local)

one sig Init_dest_pe0   extends Init {}
one sig Init_source_pe1 extends Init {}

fact program {
  po_imm = ld_local -> op_get

  issues = op_get -> ld_get + op_get -> st_get
  op_sb  = op_get -> (ld_get -> st_get)

  GetOp = op_get
  no PutOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = ld_local + st_get + Init_dest_pe0
  PE1.target_of = ld_get + Init_source_pe1

  PE0.home_of = ld_local + op_get + Init_dest_pe0
  PE1.home_of = Init_source_pe1

  same_location =
      (Init_dest_pe0 + ld_local + st_get) -> (Init_dest_pe0 + ld_local + st_get) +
      (Init_source_pe1 + ld_get) -> (Init_source_pe1 + ld_get)
}

fact atomicity {
  no (ld_local + ld_get + st_get) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// The local load observes the pre-get initial value, race-free.
run load_reads_pre_get_value {
  openshmem_memory_model
  (Init_dest_pe0 -> ld_local) in rf
  no_api_races
} for 0 but 12 Event expect 1

// The local load cannot read the get's store (ilv orders the load before it).
run load_cannot_read_get {
  openshmem_memory_model
  (st_get -> ld_local) in rf
} for 0 but 12 Event expect 0
