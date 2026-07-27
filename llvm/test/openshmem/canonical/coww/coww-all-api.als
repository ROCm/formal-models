module memory_consistency/llvm/test/openshmem/canonical/coww/coww_all_api

// Canonical CoWW / CoRR (single-location coherence) with BOTH the writes and the
// reads ordered. One PE issues two fence-separated writes to a single remote
// location (pinning the coherence order x=1 before x=2); the observer reads
// twice with a fence between the reads. Realized with remote atomic accesses
// (race-free). FORBIDS the backward outcome.
//
//   PE0: shmem_atomic_set(x, 1, pe2) ; shmem_fence() ; shmem_atomic_set(x, 2, pe2)
//   PE1: r0 = shmem_atomic_fetch(x, pe2) ; shmem_fence() ; r1 = shmem_atomic_fetch(x, pe2)
//
// Why the backward outcome (r0==2 && r1==1) is forbidden: the writes and reads
// are atomic (AMO) operations, so read-from between them yields API
// synchronizes-with (asw) edges. With st1 --rdo--> st2 (write fence) and the
// read fence giving ld_a --rdo--> ld_b, if ld_a reads st2 then
//   st1 --rdo--> st2 --asw--> ld_a --rdo--> ld_b,
// so st2 is api_hb-between st1 and ld_b. api_may_see then excludes st1 as a
// source for ld_b, so ld_b cannot read the coherence-earlier st1. Note this
// holds even under the simplified C11 axioms (no per-location total mo needed):
// the AMO asw edges carry the coherence order.

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_w1, op_fw, op_w2 extends Operation {}   // PE0: x=1 ; fence ; x=2
one sig op_ra, op_fr, op_rb extends Operation {}   // PE1: read ; fence ; read

one sig st1  extends SimpleWrite {}
one sig st2  extends SimpleWrite {}
one sig ld_a extends SimpleRead  {}
one sig ld_b extends SimpleRead  {}

one sig Init_x_pe2 extends Init {}

fact program {
  po_imm = op_w1 -> op_fw + op_fw -> op_w2
         + op_ra -> op_fr + op_fr -> op_rb

  issues = op_w1 -> st1 + op_w2 -> st2
         + op_ra -> ld_a + op_rb -> ld_b
  no op_sb

  AmoOp = op_w1 + op_w2 + op_ra + op_rb
  FenceOp = op_fw + op_fr
  no PutOp and no GetOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  no PE1.target_of
  PE2.target_of = st1 + st2 + ld_a + ld_b + Init_x_pe2

  PE0.home_of = op_w1 + op_fw + op_w2
  PE1.home_of = op_ra + op_fr + op_rb
  PE2.home_of = Init_x_pe2

  same_location =
      (Init_x_pe2 + st1 + st2 + ld_a + ld_b) -> (Init_x_pe2 + st1 + st2 + ld_a + ld_b)
}

fact atomicity {
  st1 + st2 + ld_a + ld_b in Monotonic
  no (st1 + st2 + ld_a + ld_b) & (Release + Acquire)
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. The forward (coherent) outcome is satisfiable and race-free: ld_a reads
//    st1, ld_b reads st2.
run coherent_reads {
  openshmem_memory_model
  (st1 -> ld_a) in rf
  (st2 -> ld_b) in rf
  no_api_races
} for 0 but 16 Event expect 1

// 2. The backward (incoherent) outcome is FORBIDDEN: ld_b cannot read the
//    coherence-earlier st1 once ld_a has observed st2.
run backward_outcome_forbidden {
  openshmem_memory_model
  (st2 -> ld_a) in rf
  (st1 -> ld_b) in rf
} for 0 but 16 Event expect 0

// 3. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
