module memory_consistency/llvm/test/openshmem/rdo_put_put_race

// rdo test 2: two puts to the same remote address WITHOUT a fence between them,
// issued by a single thread on PE0. With no fence there is no rdo edge, so the
// two remote stores to PE1:a are unordered -- a data race on PE1:a (two
// non-atomic writes to the same (addr,PE), not related by api_hb).
//
//   PE0:  shmem_put(dst=a, src=b, pe1)   // obs: LD b@PE0 ; ST a@PE1
//         shmem_put(dst=a, src=c, pe1)   // obs: LD c@PE0 ; ST a@PE1
//
// Note: this is a write-write race; the model's DataRaceRead flags only reads,
// so the race is witnessed structurally as two conflicting writes left unordered
// by api_hb (the api-level data-race condition of api_mem_model.tex).

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_put1, op_put2 extends Operation {}

one sig ld_b1 extends SimpleRead {}   // put1: obs LD b@PE0 (local source)
one sig st_a1 extends SimpleWrite {}  // put1: obs ST a@PE1 (remote dest)
one sig ld_c2 extends SimpleRead {}   // put2: obs LD c@PE0 (local source)
one sig st_a2 extends SimpleWrite {}  // put2: obs ST a@PE1 (remote dest)

one sig Init_b_pe0 extends Init {}
one sig Init_c_pe0 extends Init {}
one sig Init_a_pe1 extends Init {}

fact program {
  po_imm = op_put1 -> op_put2

  issues = op_put1 -> ld_b1 + op_put1 -> st_a1
         + op_put2 -> ld_c2 + op_put2 -> st_a2
  op_sb  = op_put1 -> (ld_b1 -> st_a1) + op_put2 -> (ld_c2 -> st_a2)

  PutOp = op_put1 + op_put2
  no GetOp and no AmoOp and no PutSignalOp and no SignalFetchOp
  no FenceOp and no QuietOp and no BarrierOp and no P2PSyncOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = ld_b1 + ld_c2 + Init_b_pe0 + Init_c_pe0
  PE1.target_of = st_a1 + st_a2 + Init_a_pe1

  PE0.home_of = op_put1 + op_put2 + Init_b_pe0 + Init_c_pe0
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

// Data race on PE1:a: the two conflicting non-atomic stores can be left
// unordered by api_hb (no fence => no rdo edge).
run data_race_on_a {
  openshmem_memory_model
  (st_a1 -> st_a2) not in api_hb
  (st_a2 -> st_a1) not in api_hb
} for 0 but 16 Event expect 1

// Consequence of the race: without the fence, the first put (b) can end up the
// final value, overwriting the second (c) -- the outcome the fence prevents.
run first_put_can_win {
  openshmem_memory_model
  (st_a2 -> st_a1) in mo
} for 0 but 16 Event expect 1
