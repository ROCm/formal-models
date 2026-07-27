module memory_consistency/llvm/test/openshmem/api_relations/rdo/rdo_put_fence_put

// rdo test 1: two puts to the same remote address separated by a fence, issued
// by a single thread on PE0. Remote Delivery Order (rdo) must order the first
// put's store before the second put's store (both target PE1, and put is a
// fence-ordered operation), so there is no race on PE1:a and the final value of
// PE1:a is the one delivered by the second put (from c).
//
//   PE0:  shmem_put(dst=a, src=b, pe1)   // obs: LD b@PE0 ; ST a@PE1
//         shmem_fence()
//         shmem_put(dst=a, src=c, pe1)   // obs: LD c@PE0 ; ST a@PE1
//
//   rdo (case ii): st_a1(a@PE1) --> st_a2(a@PE1)   [fence-separated puts, same PE]
//
// The "final state" checks use modification order between the puts' non-atomic
// stores, so they are C11-flavored; the ordering/no-race check uses api_hb and
// is flavor-independent.

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_put1, op_fence, op_put2 extends Operation {}

one sig ld_b1 extends SimpleRead {}   // put1: obs LD b@PE0 (local source)
one sig st_a1 extends SimpleWrite {}  // put1: obs ST a@PE1 (remote dest)
one sig ld_c2 extends SimpleRead {}   // put2: obs LD c@PE0 (local source)
one sig st_a2 extends SimpleWrite {}  // put2: obs ST a@PE1 (remote dest)

one sig Init_b_pe0 extends Init {}
one sig Init_c_pe0 extends Init {}
one sig Init_a_pe1 extends Init {}

fact program {
  po_imm = op_put1 -> op_fence + op_fence -> op_put2

  issues = op_put1 -> ld_b1 + op_put1 -> st_a1
         + op_put2 -> ld_c2 + op_put2 -> st_a2
  op_sb  = op_put1 -> (ld_b1 -> st_a1) + op_put2 -> (ld_c2 -> st_a2)

  PutOp = op_put1 + op_put2
  FenceOp = op_fence
  no GetOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = ld_b1 + ld_c2 + Init_b_pe0 + Init_c_pe0
  PE1.target_of = st_a1 + st_a2 + Init_a_pe1

  PE0.home_of = op_put1 + op_fence + op_put2 + Init_b_pe0 + Init_c_pe0
  PE1.home_of = Init_a_pe1

  same_location =
      (Init_b_pe0 + ld_b1) -> (Init_b_pe0 + ld_b1) +
      (Init_c_pe0 + ld_c2) -> (Init_c_pe0 + ld_c2) +
      (Init_a_pe1 + st_a1 + st_a2) -> (Init_a_pe1 + st_a1 + st_a2)
}

fact atomicity {
  no (ld_b1 + ld_c2 + st_a1 + st_a2) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// The two remote stores are always api_hb-ordered by rdo -- there is no
// execution in which they are unordered (i.e. no data race on PE1:a).
run writes_always_ordered {
  openshmem_memory_model
  (st_a1 -> st_a2) not in api_hb
  (st_a2 -> st_a1) not in api_hb
} for 0 but 16 Event expect 0

// The final value of PE1:a is the second put's (from c): the first store is
// modification-ordered before the second, race-free.
run final_is_c {
  openshmem_memory_model
  (st_a1 -> st_a2) in mo
  no_api_races
} for 0 but 16 Event expect 1

// The second put's store (c) cannot be overwritten by the first (b): the
// reverse modification order is forbidden by coherence over api_hb.
run c_not_overwritten {
  openshmem_memory_model
  (st_a2 -> st_a1) in mo
} for 0 but 16 Event expect 0
