module memory_consistency/llvm/test/openshmem/api_relations/lco/lco_put_nbi_store_race

// lco relaxation: the same program as lco-put-store-after-src, but the put is
// NON-BLOCKING (shmem_put_nbi). lco applies only to blocking operations, so the
// non-blocking put's local source-load is NOT ordered before the subsequent
// local store to the same buffer. The source-load and the store are then
// unordered conflicting accesses to source@PE0 -> DATA RACE. (This is the
// formal statement of "you must shmem_quiet after a non-blocking put before
// reusing the source buffer".)
//
//   PE0:  shmem_put_nbi(dest@PE1, source, PE1)  // obs: LD source@PE0 ; ST dest@PE1
//         source = 1                             // local store, same source address
//
// With the put blocking (lco present) this is race-free; making it nbi removes
// lco and introduces the race.

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
  NonBlocking = op_put              // <-- the relaxation: non-blocking put (no lco)
  no GetOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NoStore
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

// 1. A data race is reachable: without lco the put's source-load is unordered
//    with the later store to the same buffer.
run race_reachable {
  openshmem_memory_model
  not no_api_races
} for 0 but 12 Event expect 1

// 2. The put's source-load is specifically a data-race read (it could read
//    either the original value or the later store).
run source_load_races {
  openshmem_memory_model
  ld_src in DataRaceRead
} for 0 but 12 Event expect 1
