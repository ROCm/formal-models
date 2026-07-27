module memory_consistency/llvm/test/openshmem/api_relations/rco/rco_quiet_orders_put_cross_pe

// rco test: a quiet establishes cross-PE remote completion ordering that a fence
// could not. PE0 stores a locally, puts it to PE1:b, quiets, then atomic_sets a
// flag on PE2. PE2 waits on that flag, then gets PE1:b. The get is guaranteed to
// read the put's store (and hence a's value), race-free.
//
//   PE0:  a = 1                                // normal local store to a@PE0
//         shmem_put(dst=b, src=a, pe1)         // obs: LD a@PE0 ; ST b@PE1
//         shmem_quiet()
//         shmem_atomic_set(dst=c, val=1, pe2)  // obs: ST c@PE2 (atomic)
//   PE2:  shmem_wait_until(c == 1)             // obs: LD c@PE2 (atomic, local)
//         shmem_get(dst=d, src=b, pe1)         // obs: LD b@PE1 ; ST d@PE2
//
// Ordering chain (delivery of the put to the get):
//   st_a0 --ilv--> ld_a  (put reads local a=1); op_sb ld_a --> st_b (delivers 1)
//   st_b --rco(case4)--> st_c --asw--> ld_c --lco--> ld_b
// so the get's read of b@PE1 must observe the put's store.
//
// Why quiet (rco) and not a fence (rdo): st_b targets PE1 and st_c targets PE2,
// different PEs. rdo case (ii) only relates fence-separated observable accesses
// that target the SAME PE, so a fence could not order st_b before st_c; rco
// gives full connectivity across the quiet regardless of target PE.
//
// Uses only rf / api_hb / DataRaceRead (no modification order), so it is
// flavor-independent (valid under both the C11 and LLVM predicates).

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_put, op_quiet, op_set extends Operation {}   // PE0
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
  po_imm = st_a0 -> op_put + op_put -> op_quiet + op_quiet -> op_set
         + op_wait -> op_get

  issues = op_put -> ld_a + op_put -> st_b
         + op_set -> st_c
         + op_wait -> ld_c
         + op_get -> ld_b + op_get -> st_d
  op_sb  = op_put -> (ld_a -> st_b) + op_get -> (ld_b -> st_d)

  PutOp = op_put
  QuietOp = op_quiet
  AmoOp = op_set
  P2PSyncOp = op_wait
  GetOp = op_get
  no FenceOp and no BarrierOp and no PutSignalOp and no SignalFetchOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = st_a0 + ld_a + Init_a_pe0
  PE1.target_of = st_b + ld_b + Init_b_pe1
  PE2.target_of = st_c + ld_c + st_d + Init_c_pe2 + Init_d_pe2

  PE0.home_of = st_a0 + op_put + op_quiet + op_set + Init_a_pe0
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

// The intended race-free execution exists: the get reads the put's store to
// PE1:b (which carries a's value).
run good_outcome {
  openshmem_memory_model
  (st_c -> ld_c) in rf     // wait observes the flag
  (st_a0 -> ld_a) in rf    // put reads local a = 1
  (st_b -> ld_b) in rf     // get reads the put's store
  no_api_races
} for 0 but 22 Event expect 1

// Guarantee: given the wait observes the flag, the get cannot read the stale
// initial value of PE1:b -- the quiet's rco ordering delivers the put.
run get_loads_put_not_stale {
  openshmem_memory_model
  (st_c -> ld_c) in rf
  (Init_b_pe1 -> ld_b) in rf
} for 0 but 22 Event expect 0

// The value delivered is a=1: the put's source-load cannot read the stale
// initial value of a@PE0 (ilv), so st_b carries a's value.
run put_loaded_local_store {
  openshmem_memory_model
  (st_c -> ld_c) in rf
  (Init_a_pe0 -> ld_a) in rf
} for 0 but 22 Event expect 0
