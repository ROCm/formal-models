module memory_consistency/llvm/test/openshmem/api_relations/rdo/rdo_nofence_store_local_sync_race

// Variant of the local-sync rdo test with the PE0 fence REMOVED. Without the
// fence there is no rdo edge ordering the prior normal store (st_a0) before the
// atomic_set's store (st_b). So even though PE1's local wait synchronizes with
// the atomic_set and lco orders the wait before the get, st_a0 is not ordered
// before the get's read of a@PE0 -> a data race on PE0:a.
//
//   PE0:  a = 1                               // normal local store to a@PE0
//         shmem_atomic_set(dst=b, val=1, pe1)  // obs: ST b@PE1 (atomic)   [NO FENCE]
//   PE1:  shmem_wait_until(b == 1)             // obs: LD b@PE1 (atomic, local)
//         shmem_get(dst=a, src=a, pe0)         // obs: LD a@PE0 ; ST a@PE1
//         x = a                                // local load of a@PE1

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_set extends Operation {}             // PE0 (no fence)
one sig op_wait, op_get extends Operation {}    // PE1

one sig st_a0 extends SimpleWrite {}
one sig st_b  extends SimpleWrite {}
one sig ld_b  extends SimpleRead {}
one sig ld_a_src extends SimpleRead {}
one sig st_a_dst extends SimpleWrite {}
one sig ld_final extends SimpleRead {}

one sig Init_a_pe0 extends Init {}
one sig Init_b_pe1 extends Init {}
one sig Init_a_pe1 extends Init {}

fact program {
  po_imm = st_a0 -> op_set
         + op_wait -> op_get + op_get -> ld_final

  issues = op_set -> st_b + op_wait -> ld_b
         + op_get -> ld_a_src + op_get -> st_a_dst
  op_sb  = op_get -> (ld_a_src -> st_a_dst)

  AmoOp = op_set
  P2PSyncOp = op_wait
  GetOp = op_get
  no PutOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = st_a0 + ld_a_src + Init_a_pe0
  PE1.target_of = st_b + ld_b + st_a_dst + ld_final + Init_b_pe1 + Init_a_pe1

  PE0.home_of = st_a0 + op_set + Init_a_pe0
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

// Without the fence, the get's read of a@PE0 races with the prior store.
run race_on_a {
  openshmem_memory_model
  (st_b -> ld_b) in rf
  ld_a_src in DataRaceRead
} for 0 but 20 Event expect 1

// ...and there is no race-free execution delivering PE0's store to the get.
run no_racefree_delivery {
  openshmem_memory_model
  (st_b -> ld_b) in rf
  (st_a0 -> ld_a_src) in rf
  no_api_races
} for 0 but 20 Event expect 0
