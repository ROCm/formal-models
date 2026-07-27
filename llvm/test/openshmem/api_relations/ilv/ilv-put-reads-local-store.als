module memory_consistency/llvm/test/openshmem/api_relations/ilv/ilv_put_reads_local_store

// ilv test 1: a store to local memory followed by a put that reads the same
// (local source) address. Implicit Local Visibility (ilv) must order the local
// store before the put's observable source-load, so the put reads the store,
// not the stale initial value. No data race.
//
//   PE0:  source = 1                         // local store
//         shmem_put(dest@PE1, source, PE1)   // obs: LD source@PE0 ; ST dest@PE1
//
//   ilv: st_local(source@PE0) --> ld_src(source@PE0)   [both local to caller PE0]

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_put extends Operation {}

one sig st_local extends SimpleWrite {}  // PE0: local store to source@PE0
one sig ld_src   extends SimpleRead {}   // put: observable LD source@PE0 (local)
one sig st_dst   extends SimpleWrite {}  // put: observable ST dest@PE1 (remote)

one sig Init_source_pe0 extends Init {}
one sig Init_dest_pe1   extends Init {}

fact program {
  po_imm = st_local -> op_put

  issues = op_put -> ld_src + op_put -> st_dst
  op_sb  = op_put -> (ld_src -> st_dst)

  PutOp = op_put
  no GetOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = st_local + ld_src + Init_source_pe0
  PE1.target_of = st_dst + Init_dest_pe1

  PE0.home_of = st_local + op_put + Init_source_pe0
  PE1.home_of = Init_dest_pe1

  same_location =
      (Init_source_pe0 + st_local + ld_src) -> (Init_source_pe0 + st_local + ld_src) +
      (Init_dest_pe1 + st_dst) -> (Init_dest_pe1 + st_dst)
}

fact atomicity {
  // put is bulk RMA: all accesses here are non-atomic.
  no (st_local + ld_src + st_dst) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// The put's source-load reads the local store, race-free.
// 1. Expected behavior is satisfiable: the put's source-load reads the store.
run can_read_from_st_local {
  openshmem_memory_model
  (st_local -> ld_src) in rf
} for 0 but 12 Event expect 1

// 2. No alternative to the expected behavior: the source-load reads the store
//    in every legal execution.
run cannot_not_read_from_st_local {
  openshmem_memory_model
  (st_local -> ld_src) not in rf
} for 0 but 12 Event expect 0

// 3. No data race in any legal execution.
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 12 Event expect 0
