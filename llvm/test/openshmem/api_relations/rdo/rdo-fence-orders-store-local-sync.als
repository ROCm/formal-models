module memory_consistency/llvm/test/openshmem/api_relations/rdo/rdo_fence_orders_store_local_sync

// rdo test (fence orders a prior NORMAL store): PE0 stores to a local address,
// fences, then atomic_sets a flag on PE1; PE1 waits on that (local) flag, gets a
// from PE0, and loads it. The fence orders the prior normal store before the
// atomic_set (rdo case i), which synchronizes with the wait (asw), which orders
// the subsequent get (lco), so the get reads PE0's stored value and the final
// load returns it. No data race.
//
//   PE0:  a = 1                              // normal local store to a@PE0
//         shmem_fence()
//         shmem_atomic_set(dst=b, val=1, pe1) // obs: ST b@PE1 (atomic)
//   PE1:  shmem_wait_until(b == 1)            // obs: LD b@PE1 (atomic, local)
//         shmem_get(dst=a, src=a, pe0)        // obs: LD a@PE0 ; ST a@PE1
//         x = a                               // local load of a@PE1
//
//   st_a0 --rdo(i)--> st_b --asw--> ld_b --lco--> ld_a_src ... st_a_dst --lco--> ld_final

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_fence, op_set extends Operation {}   // PE0
one sig op_wait, op_get  extends Operation {}   // PE1

one sig st_a0 extends SimpleWrite {}   // PE0: normal store to a@PE0
one sig st_b  extends SimpleWrite {}   // atomic_set: obs ST b@PE1 (atomic)
one sig ld_b  extends SimpleRead {}    // wait_until: obs LD b@PE1 (atomic, local)
one sig ld_a_src extends SimpleRead {} // get: obs LD a@PE0 (remote source)
one sig st_a_dst extends SimpleWrite {}// get: obs ST a@PE1 (local dest)
one sig ld_final extends SimpleRead {} // PE1: normal load of a@PE1

one sig Init_a_pe0 extends Init {}
one sig Init_b_pe1 extends Init {}
one sig Init_a_pe1 extends Init {}

fact program {
  po_imm = st_a0 -> op_fence + op_fence -> op_set
         + op_wait -> op_get + op_get -> ld_final

  issues = op_set -> st_b + op_wait -> ld_b
         + op_get -> ld_a_src + op_get -> st_a_dst
  op_sb  = op_get -> (ld_a_src -> st_a_dst)

  AmoOp = op_set
  FenceOp = op_fence
  P2PSyncOp = op_wait
  GetOp = op_get
  no PutOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = st_a0 + ld_a_src + Init_a_pe0
  PE1.target_of = st_b + ld_b + st_a_dst + ld_final + Init_b_pe1 + Init_a_pe1

  PE0.home_of = st_a0 + op_fence + op_set + Init_a_pe0
  PE1.home_of = op_wait + op_get + ld_final + Init_b_pe1 + Init_a_pe1

  same_location =
      (Init_a_pe0 + st_a0 + ld_a_src) -> (Init_a_pe0 + st_a0 + ld_a_src) +
      (Init_b_pe1 + st_b + ld_b) -> (Init_b_pe1 + st_b + ld_b) +
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

// The intended race-free execution exists: the get reads PE0's store and the
// final load returns it.
run good_outcome {
  openshmem_memory_model
  (st_b -> ld_b) in rf
  (st_a0 -> ld_a_src) in rf
  (st_a_dst -> ld_final) in rf
  no_api_races
} for 0 but 20 Event expect 1

// Given the wait observes the flag, the get cannot read the stale initial value
// of a@PE0 -- the store is ordered transitively (rdo -> asw -> lco).
run get_reads_pe0_store {
  openshmem_memory_model
  (st_b -> ld_b) in rf
  (Init_a_pe0 -> ld_a_src) in rf
} for 0 but 20 Event expect 0

// ...and the final local load cannot read the stale initial value of a@PE1.
run final_load_returns_stored {
  openshmem_memory_model
  (st_b -> ld_b) in rf
  (Init_a_pe1 -> ld_final) in rf
} for 0 but 20 Event expect 0
