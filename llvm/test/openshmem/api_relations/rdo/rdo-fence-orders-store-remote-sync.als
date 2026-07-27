module memory_consistency/llvm/test/openshmem/api_relations/rdo/rdo_fence_orders_store_remote_sync

// rdo test (fence orders a prior NORMAL store, synchronization through a THIRD
// PE): as the local-sync version, but the flag lives on PE2 -- PE0 atomic_sets
// b@PE2, and PE1 synchronizes with a REMOTE atomic_fetch of b@PE2 (instead of a
// local wait_until). This probes whether remote-fetch synchronization still
// orders the subsequent remote get.
//
//   PE0:  a = 1                               // normal local store to a@PE0
//         shmem_fence()
//         shmem_atomic_set(dst=b, val=1, pe2)  // obs: ST b@PE2 (atomic)
//   PE1:  r = shmem_atomic_fetch(src=b, pe2)   // obs: LD b@PE2 (atomic, REMOTE)
//         shmem_get(dst=a, src=a, pe0)         // obs: LD a@PE0 ; ST a@PE1
//         x = a                                // local load of a@PE1
//
// FINDING: unlike the local-wait version, this is a DATA RACE per the model.
// The chain st_a0 --rdo--> st_b --asw--> ld_b establishes that PE1's fetch
// observed the flag, but the ordering does NOT reach the subsequent get's remote
// read of a@PE0. lco (which carried the ordering in the local-wait version) only
// relates a blocking operation's LOCAL observable accesses to subsequent events;
// the atomic_fetch's observable read of b@PE2 is REMOTE, so lco does not apply,
// and no other relation orders ld_a_src. Hence the get's read of a@PE0 is
// unordered w.r.t. st_a0 -> an api-level data race. (To order a subsequent
// remote get after a remote-fetch synchronization, PE1 would need a quiet or
// barrier, which give rco's full connectivity; a fence would not suffice, since
// rdo case ii requires the observable accesses to target the same PE.)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_fence, op_set extends Operation {}   // PE0
one sig op_fetch, op_get extends Operation {}   // PE1

one sig st_a0 extends SimpleWrite {}   // PE0: normal store to a@PE0
one sig st_b  extends SimpleWrite {}   // atomic_set: obs ST b@PE2 (atomic)
one sig ld_b  extends SimpleRead {}    // atomic_fetch: obs LD b@PE2 (atomic, REMOTE)
one sig ld_a_src extends SimpleRead {} // get: obs LD a@PE0 (remote source)
one sig st_a_dst extends SimpleWrite {}// get: obs ST a@PE1 (local dest)
one sig ld_final extends SimpleRead {} // PE1: normal load of a@PE1

one sig Init_a_pe0 extends Init {}
one sig Init_b_pe2 extends Init {}
one sig Init_a_pe1 extends Init {}

fact program {
  po_imm = st_a0 -> op_fence + op_fence -> op_set
         + op_fetch -> op_get + op_get -> ld_final

  issues = op_set -> st_b + op_fetch -> ld_b
         + op_get -> ld_a_src + op_get -> st_a_dst
  op_sb  = op_get -> (ld_a_src -> st_a_dst)

  AmoOp = op_set + op_fetch         // atomic_set and atomic_fetch are AMOs
  FenceOp = op_fence
  GetOp = op_get
  no PutOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = st_a0 + ld_a_src + Init_a_pe0
  PE1.target_of = st_a_dst + ld_final + Init_a_pe1
  PE2.target_of = st_b + ld_b + Init_b_pe2

  PE0.home_of = st_a0 + op_fence + op_set + Init_a_pe0
  PE1.home_of = op_fetch + op_get + ld_final + Init_a_pe1
  PE2.home_of = Init_b_pe2

  same_location =
      (Init_a_pe0 + st_a0 + ld_a_src) -> (Init_a_pe0 + st_a0 + ld_a_src) +
      (Init_b_pe2 + st_b + ld_b) -> (Init_b_pe2 + st_b + ld_b) +
      (Init_a_pe1 + st_a_dst + ld_final) -> (Init_a_pe1 + st_a_dst + ld_final)
}

fact atomicity {
  st_b + ld_b in Monotonic
  no (st_b + ld_b) & (Release + Acquire)
  no (st_a0 + ld_a_src + st_a_dst + ld_final) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// No race-free execution in which the get reads PE0's store exists: the remote
// fetch does not order the subsequent remote get, so reading st_a0 is only
// possible as a data race.
run no_racefree_delivery {
  openshmem_memory_model
  (st_b -> ld_b) in rf
  (st_a0 -> ld_a_src) in rf
  no_api_races
} for 0 but 20 Event expect 0

// Even with the flag observed, the get's remote read of a@PE0 is a data race.
run get_read_races {
  openshmem_memory_model
  (st_b -> ld_b) in rf
  ld_a_src in DataRaceRead
} for 0 but 20 Event expect 1
