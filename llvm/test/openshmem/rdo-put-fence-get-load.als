module memory_consistency/llvm/test/openshmem/rdo_put_fence_get_load

// rdo test 3: a put to a remote address, a fence, then a get reading back that
// remote address, then a local load of the get's destination -- all on a single
// PE0 thread. The data a is copied PE0 -> PE1:b (put) -> PE0:c (get) -> read.
// rdo orders the put's store to PE1:b before the get's load of PE1:b, and lco
// orders the get's local store to c before the final load, so the final load
// returns a's original value delivered through PE1:b. No race.
//
//   PE0:  shmem_put(dst=b, src=a, pe1)   // obs: LD a@PE0 ; ST b@PE1
//         shmem_fence()
//         shmem_get(dst=c, src=b, pe1)   // obs: LD b@PE1 ; ST c@PE0
//         x = c                          // local load of c@PE0
//
//   rdo (case ii): st_b(b@PE1) --> ld_b(b@PE1)     [fence-separated, same PE]
//   lco:           st_c(c@PE0) --> ld_final(c@PE0) [blocking get completes locally]
//
// All checks are api_hb / rf based (no mo), so this test is flavor-independent
// (runs under both the C11 and LLVM predicates).

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_put, op_fence, op_get extends Operation {}

one sig ld_a extends SimpleRead {}    // put: obs LD a@PE0 (local source)
one sig st_b extends SimpleWrite {}   // put: obs ST b@PE1 (remote dest)
one sig ld_b extends SimpleRead {}    // get: obs LD b@PE1 (remote source)
one sig st_c extends SimpleWrite {}   // get: obs ST c@PE0 (local dest)
one sig ld_final extends SimpleRead {} // PE0: local load of c@PE0

one sig Init_a_pe0 extends Init {}
one sig Init_b_pe1 extends Init {}
one sig Init_c_pe0 extends Init {}

fact program {
  po_imm = op_put -> op_fence + op_fence -> op_get + op_get -> ld_final

  issues = op_put -> ld_a + op_put -> st_b + op_get -> ld_b + op_get -> st_c
  op_sb  = op_put -> (ld_a -> st_b) + op_get -> (ld_b -> st_c)

  PutOp = op_put
  GetOp = op_get
  FenceOp = op_fence
  no AmoOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore     // blocking put and get
}

fact locations_and_pes {
  PE0.target_of = ld_a + st_c + ld_final + Init_a_pe0 + Init_c_pe0
  PE1.target_of = st_b + ld_b + Init_b_pe1

  PE0.home_of = op_put + op_fence + op_get + ld_final + Init_a_pe0 + Init_c_pe0
  PE1.home_of = Init_b_pe1

  same_location =
      (Init_a_pe0 + ld_a) -> (Init_a_pe0 + ld_a) +
      (Init_b_pe1 + st_b + ld_b) -> (Init_b_pe1 + st_b + ld_b) +
      (Init_c_pe0 + st_c + ld_final) -> (Init_c_pe0 + st_c + ld_final)
}

fact atomicity {
  no (ld_a + st_b + ld_b + st_c + ld_final) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// The intended ordered copy chain exists and is race-free: the get reads the
// put's delivered value and the final load reads the get's delivered value.
run ordered_chain_exists {
  openshmem_memory_model
  (Init_a_pe0 -> ld_a) in rf
  (st_b -> ld_b) in rf
  (st_c -> ld_final) in rf
  no_api_races
} for 0 but 16 Event expect 1

// The get's load of PE1:b cannot read the stale initial value: rdo orders the
// put's store before it.
run get_reads_delivered_b {
  openshmem_memory_model
  (Init_b_pe1 -> ld_b) in rf
} for 0 but 16 Event expect 0

// The final local load of c cannot read the stale initial value: lco orders the
// get's local store before it.
run final_load_reads_delivered_c {
  openshmem_memory_model
  (Init_c_pe0 -> ld_final) in rf
} for 0 but 16 Event expect 0
