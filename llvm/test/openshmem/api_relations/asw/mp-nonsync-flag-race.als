module memory_consistency/llvm/test/openshmem/api_relations/asw/mp_nonsync_flag_race

// asw relaxation: the same MP idiom as put-fence-flag, but the flag is raised and
// consumed with NON-synchronizing (normal, non-atomic) accesses instead of
// shmem_atomic_set / shmem_wait_until. API synchronizes-with (asw) relates the
// observable write and read of a synchronizing operation category (AMO / signal /
// p2p-sync / lock); a plain remote store and a plain load are not in any such
// category, so NO asw edge is formed. Even when PE1 observes the raised flag,
// nothing orders PE0's data delivery before PE1's read of data -> DATA RACE.
//
//   PE0:  shmem_put(data, ...)      // obs: LD src@PE0 ; ST data@PE1
//         shmem_fence()
//         *flag_on_pe1 = 1          // NORMAL remote store ST flag@PE1 (non-atomic)
//   PE1:  r = flag                  // NORMAL local load LD flag@PE1
//         x = data                  // NORMAL local load LD data@PE1
//
// The fence still gives rdo st_dst --> st_flag (same target PE1), but the chain
// stops there: st_flag --(no asw)--> load_flag, so the data read is unordered
// with the put. Contrast put-fence-flag, where an atomic flag supplies asw and
// the program is race-free.

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_put, op_fence, op_pflag extends Operation {}   // PE0

one sig ld_src   extends SimpleRead {}   // put: obs LD data@PE0 (local source)
one sig st_dst   extends SimpleWrite {}  // put: obs ST data@PE1 (remote dest)
one sig st_flag  extends SimpleWrite {}  // p (single-word put): obs ST flag@PE1 (NORMAL)
one sig load_flag extends SimpleRead {}  // PE1: normal local load of flag@PE1
one sig load_data extends SimpleRead {}  // PE1: normal local load of data@PE1

one sig Init_data_pe0 extends Init {}
one sig Init_data_pe1 extends Init {}
one sig Init_flag_pe1 extends Init {}

fact program {
  po_imm = op_put -> op_fence + op_fence -> op_pflag + load_flag -> load_data

  issues = op_put -> ld_src + op_put -> st_dst
         + op_pflag -> st_flag
  op_sb  = op_put -> (ld_src -> st_dst)

  PutOp = op_put + op_pflag          // both are (non-synchronizing) puts
  FenceOp = op_fence
  no GetOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = ld_src + Init_data_pe0
  PE1.target_of = st_dst + st_flag + load_flag + load_data
                  + Init_data_pe1 + Init_flag_pe1

  PE0.home_of = op_put + op_fence + op_pflag + Init_data_pe0
  PE1.home_of = load_flag + load_data + Init_data_pe1 + Init_flag_pe1

  same_location =
      (Init_data_pe0 + ld_src) -> (Init_data_pe0 + ld_src) +
      (Init_data_pe1 + st_dst + load_data) -> (Init_data_pe1 + st_dst + load_data) +
      (Init_flag_pe1 + st_flag + load_flag) -> (Init_flag_pe1 + st_flag + load_flag)
}

fact atomicity {
  no (ld_src + st_dst + st_flag + load_flag + load_data) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. A data race is reachable: the non-atomic flag forms no asw, so the MP idiom
//    is unsynchronized.
run race_reachable {
  openshmem_memory_model
  not no_api_races
} for 0 but 12 Event expect 1

// 2. The consumer's read of data is specifically a data-race read (nothing
//    orders the put's delivery before it).
run data_read_races {
  openshmem_memory_model
  load_data in DataRaceRead
} for 0 but 12 Event expect 1

// 3. There is NO race-free execution: without asw the flag never establishes
//    synchronization, so some access always races. (Contrast put-fence-flag,
//    which has a race-free execution once the atomic flag supplies asw.)
run no_racefree_execution {
  openshmem_memory_model
  no_api_races
} for 0 but 12 Event expect 0
