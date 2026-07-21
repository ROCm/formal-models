module memory_consistency/llvm/test/openshmem/rdo_put_get_load_race

// rdo test 4: the copy chain of test 3 WITHOUT the fence between the put and the
// get. With no fence there is no rdo edge, so the put's store to PE1:b is
// unordered w.r.t. the get's load of PE1:b -- a data race on PE1:b. The get's
// observable load of b then reads undef (a DataRaceRead).
//
//   PE0:  shmem_put(dst=b, src=a, pe1)   // obs: LD a@PE0 ; ST b@PE1
//         shmem_get(dst=c, src=b, pe1)   // obs: LD b@PE1 ; ST c@PE0
//         x = c                          // local load of c@PE0
//
// The race involves the get's read of PE1:b, so it is witnessed as a
// DataRaceRead (flavor-independent).

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_put, op_get extends Operation {}

one sig ld_a extends SimpleRead {}    // put: obs LD a@PE0 (local source)
one sig st_b extends SimpleWrite {}   // put: obs ST b@PE1 (remote dest)
one sig ld_b extends SimpleRead {}    // get: obs LD b@PE1 (remote source)
one sig st_c extends SimpleWrite {}   // get: obs ST c@PE0 (local dest)
one sig ld_final extends SimpleRead {} // PE0: local load of c@PE0

one sig Init_a_pe0 extends Init {}
one sig Init_b_pe1 extends Init {}
one sig Init_c_pe0 extends Init {}

fact program {
  po_imm = op_put -> op_get + op_get -> ld_final

  issues = op_put -> ld_a + op_put -> st_b + op_get -> ld_b + op_get -> st_c
  op_sb  = op_put -> (ld_a -> st_b) + op_get -> (ld_b -> st_c)

  PutOp = op_put
  GetOp = op_get
  no AmoOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore     // blocking put and get
}

fact locations_and_pes {
  PE0.target_of = ld_a + st_c + ld_final + Init_a_pe0 + Init_c_pe0
  PE1.target_of = st_b + ld_b + Init_b_pe1

  PE0.home_of = op_put + op_get + ld_final + Init_a_pe0 + Init_c_pe0
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

// Data race on PE1:b: without the fence, the get's observable load of b races
// with the put's observable store to b and reads undef.
run race_on_b {
  openshmem_memory_model
  ld_b in DataRaceRead
} for 0 but 16 Event expect 1
