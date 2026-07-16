module memory_consistency/llvm/test/openshmem/lco_get_load_after_dst

// lco test 2: a blocking get followed by a local load of the get's destination
// address. Local Completion Order (lco) must order the get's local destination-
// store before the subsequent local load, so the load must observe the value
// the get delivered (the blocking get completes its local store before the
// later load). No data race.
//
//   PE0:  shmem_get(dest, source@PE1, PE1)    // obs: LD source@PE1 ; ST dest@PE0
//         x = dest                            // local load, same dest address
//
//   lco: st_get(dest@PE0) --> ld_after(dest@PE0)   [blocking get, local]

open memory_consistency/llvm/openshmem_predicates

one sig PE0, PE1 extends PE {}

one sig op_get extends Operation {}

one sig ld_get   extends SimpleRead {}   // get: observable LD source@PE1 (remote)
one sig st_get   extends SimpleWrite {}  // get: observable ST dest@PE0 (local)
one sig ld_after extends SimpleRead {}   // PE0: local load of dest@PE0 after the get

one sig Init_dest_pe0   extends Init {}
one sig Init_source_pe1 extends Init {}

fact program {
  po_imm = op_get -> ld_after

  issues = op_get -> ld_get + op_get -> st_get
  op_sb  = op_get -> (ld_get -> st_get)

  GetOp = op_get
  no PutOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore     // blocking get
}

fact locations_and_pes {
  PE0.target_of = st_get + ld_after + Init_dest_pe0
  PE1.target_of = ld_get + Init_source_pe1

  PE0.home_of = op_get + ld_after + Init_dest_pe0
  PE1.home_of = Init_source_pe1

  same_location =
      (Init_dest_pe0 + st_get + ld_after) -> (Init_dest_pe0 + st_get + ld_after) +
      (Init_source_pe1 + ld_get) -> (Init_source_pe1 + ld_get)
}

fact atomicity {
  no (ld_get + st_get + ld_after) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// The later local load observes the get's store, race-free.
run get_load_reads_get_store {
  openshmem_memory_model
  (st_get -> ld_after) in rf
  no_api_races
} for 0 but 12 Event expect 1

// The later local load cannot read the stale initial value (lco orders the
// blocking get's store before the load).
run get_load_cannot_read_init {
  openshmem_memory_model
  (Init_dest_pe0 -> ld_after) in rf
} for 0 but 12 Event expect 0
