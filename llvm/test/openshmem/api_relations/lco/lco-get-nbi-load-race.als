module memory_consistency/llvm/test/openshmem/api_relations/lco/lco_get_nbi_load_race

// lco relaxation: the same program as lco-get-load-after-dst, but the get is
// NON-BLOCKING (shmem_get_nbi). lco applies only to blocking operations, so the
// non-blocking get's local destination-store is NOT ordered before the
// subsequent local load of the same buffer. The local load and the get's store
// are then unordered conflicting accesses to dest@PE0 -> DATA RACE. (Formal
// statement of "you must shmem_quiet after a non-blocking get before reading the
// destination buffer".)
//
//   PE0:  shmem_get_nbi(dest, source@PE1, PE1)  // obs: LD source@PE1 ; ST dest@PE0
//         x = dest                              // local load, same dest address
//
// With the get blocking (lco present) the load must read the get's store,
// race-free; making it nbi removes lco and introduces the race.

open memory_consistency/llvm/openshmem_predicates_c11

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
  NonBlocking = op_get              // <-- the relaxation: non-blocking get (no lco)
  no PutOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NoStore
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

// 1. A data race is reachable: without lco the get's destination-store is
//    unordered with the later local load of the same buffer.
run race_reachable {
  openshmem_memory_model
  not no_api_races
} for 0 but 12 Event expect 1

// 2. The later local load is specifically a data-race read (it could read either
//    the stale initial value or the get's store).
run later_load_races {
  openshmem_memory_model
  ld_after in DataRaceRead
} for 0 but 12 Event expect 1
