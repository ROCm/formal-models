module memory_consistency/llvm/test/openshmem/api_relations/rco/rco_fence_insufficient_cross_pe_race

// rco relaxation: the same program as rco-quiet-orders-put-cross-pe, but the
// shmem_quiet is replaced by a shmem_fence. This is the negative companion that
// shows why the quiet (rco) was needed: the put's store targets PE1 (b@PE1) and
// the atomic_set's store targets PE2 (c@PE2) -- DIFFERENT PEs. rdo case (ii) only
// orders fence-separated observable accesses that target the SAME PE, so the
// fence does NOT order st_b before st_c. The flag can therefore be observed
// before the put is delivered, and the consumer's get of b@PE1 races with the
// put's store -> DATA RACE.
//
//   PE0:  a = 1
//         shmem_put(dst=b, src=a, pe1)         // obs: LD a@PE0 ; ST b@PE1
//         shmem_fence()                         // <-- was shmem_quiet()
//         shmem_atomic_set(dst=c, val=1, pe2)  // obs: ST c@PE2 (atomic)
//   PE2:  shmem_wait_until(c == 1)             // obs: LD c@PE2 (atomic, local)
//         shmem_get(dst=d, src=b, pe1)         // obs: LD b@PE1 ; ST d@PE2
//
// (The fence still gives rdo case (i) st_a0 --> st_c, and rco/quiet would give
// full cross-PE connectivity st_b --> st_c, but the fence cannot cross PEs.)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_put, op_fence, op_set extends Operation {}   // PE0
one sig op_wait, op_get extends Operation {}            // PE2

one sig st_a0 extends SimpleWrite {}   // PE0: normal store to a@PE0
one sig ld_a  extends SimpleRead {}    // put: obs LD a@PE0 (local source)
one sig st_b  extends SimpleWrite {}   // put: obs ST b@PE1 (remote dest)
one sig st_c  extends SimpleWrite {}   // atomic_set: obs ST c@PE2 (atomic)
one sig ld_c  extends SimpleRead {}    // wait_until: obs LD c@PE2 (atomic, local)
one sig ld_b  extends SimpleRead {}    // get: obs LD b@PE1 (remote source)
one sig st_d  extends SimpleWrite {}   // get: obs ST d@PE2 (local dest)

one sig Init_a_pe0 extends Init {}
one sig Init_b_pe1 extends Init {}
one sig Init_c_pe2 extends Init {}
one sig Init_d_pe2 extends Init {}

fact program {
  po_imm = st_a0 -> op_put + op_put -> op_fence + op_fence -> op_set
         + op_wait -> op_get

  issues = op_put -> ld_a + op_put -> st_b
         + op_set -> st_c
         + op_wait -> ld_c
         + op_get -> ld_b + op_get -> st_d
  op_sb  = op_put -> (ld_a -> st_b) + op_get -> (ld_b -> st_d)

  PutOp = op_put
  FenceOp = op_fence                 // <-- was QuietOp
  AmoOp = op_set
  P2PSyncOp = op_wait
  GetOp = op_get
  no QuietOp and no BarrierOp and no PutSignalOp and no SignalFetchOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = st_a0 + ld_a + Init_a_pe0
  PE1.target_of = st_b + ld_b + Init_b_pe1
  PE2.target_of = st_c + ld_c + st_d + Init_c_pe2 + Init_d_pe2

  PE0.home_of = st_a0 + op_put + op_fence + op_set + Init_a_pe0
  PE1.home_of = Init_b_pe1
  PE2.home_of = op_wait + op_get + Init_c_pe2 + Init_d_pe2

  same_location =
      (Init_a_pe0 + st_a0 + ld_a) -> (Init_a_pe0 + st_a0 + ld_a) +
      (Init_b_pe1 + st_b + ld_b) -> (Init_b_pe1 + st_b + ld_b) +
      (Init_c_pe2 + st_c + ld_c) -> (Init_c_pe2 + st_c + ld_c) +
      (Init_d_pe2 + st_d) -> (Init_d_pe2 + st_d)
}

fact atomicity {
  st_c + ld_c in Monotonic
  no (st_c + ld_c) & (Release + Acquire)
  no (st_a0 + ld_a + st_b + ld_b + st_d) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. Even when the wait observes the flag, the get's read of b@PE1 is a data-race
//    read: the fence could not order the put's cross-PE delivery before the flag.
run get_read_races {
  openshmem_memory_model
  (st_c -> ld_c) in rf
  ld_b in DataRaceRead
} for 0 but 22 Event expect 1

// 2. No race-free execution delivers the put to the get (that would require rco).
run no_racefree_delivery {
  openshmem_memory_model
  (st_c -> ld_c) in rf
  (st_b -> ld_b) in rf
  no_api_races
} for 0 but 22 Event expect 0
