module memory_consistency/llvm/test/openshmem/lco_put_store_after_src

// lco test 1: a blocking put followed by a local store to the put's source
// address. Local Completion Order (lco) must order the put's local source-load
// before the subsequent local store, so the put's load cannot observe that
// later store (the blocking put completes its source read before the store
// overwrites the buffer). No data race.
//
//   PE0:  shmem_put(dest@PE1, source, PE1)   // obs: LD source@PE0 ; ST dest@PE1
//         source = 1                          // local store, same source address
//
//   lco: ld_src(source@PE0) --> st_after(source@PE0)   [blocking put, local]

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_put extends Operation {}

one sig ld_src   extends SimpleRead {}   // put: observable LD source@PE0 (local)
one sig st_dst   extends SimpleWrite {}  // put: observable ST dest@PE1 (remote)
one sig st_after extends SimpleWrite {}  // PE0: local store to source@PE0 after the put

one sig Init_source_pe0 extends Init {}
one sig Init_dest_pe1   extends Init {}

fact program {
  po_imm = op_put -> st_after

  issues = op_put -> ld_src + op_put -> st_dst
  op_sb  = op_put -> (ld_src -> st_dst)

  PutOp = op_put
  no GetOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore     // blocking put
}

fact locations_and_pes {
  PE0.target_of = ld_src + st_after + Init_source_pe0
  PE1.target_of = st_dst + Init_dest_pe1

  PE0.home_of = op_put + st_after + Init_source_pe0
  PE1.home_of = Init_dest_pe1

  same_location =
      (Init_source_pe0 + ld_src + st_after) -> (Init_source_pe0 + ld_src + st_after) +
      (Init_dest_pe1 + st_dst) -> (Init_dest_pe1 + st_dst)
}

fact atomicity {
  no (ld_src + st_dst + st_after) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// The put's source-load reads the original source value, race-free.
run put_load_reads_original {
  openshmem_memory_model
  (Init_source_pe0 -> ld_src) in rf
  no_api_races
} for 0 but 12 Event expect 1

// The put's source-load cannot read the later local store (lco orders the
// blocking put's load before it).
run put_load_cannot_read_later_store {
  openshmem_memory_model
  (st_after -> ld_src) in rf
} for 0 but 12 Event expect 0
