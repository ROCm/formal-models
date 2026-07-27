module memory_consistency/llvm/test/openshmem/canonical/coww/coww_relaxed

// Canonical CoWW / CoRR (single-location coherence). One PE issues two ordered
// writes to a single remote location (a fence between them pins the coherence
// order x=1 --before-- x=2); an observer reads the location twice. Realized with
// remote atomic accesses (race-free).
//
// Classic CoWW:
//   P0: x = 1 ; x = 2            (coherence order: 1 then 2)
//   P1: r0 = x ; r1 = x
// "Backward" outcome (reads go against the coherence order): r0==2 && r1==1.
//
//   PE0: shmem_atomic_set(x, 1, pe2) ; shmem_fence() ; shmem_atomic_set(x, 2, pe2)
//   PE1: r0 = shmem_atomic_fetch(x, pe2) ; r1 = shmem_atomic_fetch(x, pe2)   // NO fence
//
// The observer's two reads are program-order-exempt and, with NO fence between
// them, are not hb-ordered. So even though the writes are coherence-ordered, the
// backward read outcome is ALLOWED: the read-read coherence (CoRR) rule needs the
// two reads ordered to bite. (See coww-all-api.als / coww-llvm-coherent.als for
// the fenced-reads cases.)

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1, PE2 extends PE {}

one sig op_w1, op_fw, op_w2 extends Operation {}   // PE0: x=1 ; fence ; x=2
one sig op_ra, op_rb extends Operation {}          // PE1: read ; read

one sig st1  extends SimpleWrite {}   // atomic_set x=1 (P0)
one sig st2  extends SimpleWrite {}   // atomic_set x=2 (P0)
one sig ld_a extends SimpleRead  {}   // atomic_fetch x (P1, first)
one sig ld_b extends SimpleRead  {}   // atomic_fetch x (P1, second)

one sig Init_x_pe2 extends Init {}

fact program {
  po_imm = op_w1 -> op_fw + op_fw -> op_w2 + op_ra -> op_rb

  issues = op_w1 -> st1 + op_w2 -> st2
         + op_ra -> ld_a + op_rb -> ld_b
  no op_sb

  AmoOp = op_w1 + op_w2 + op_ra + op_rb
  FenceOp = op_fw
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
  PE1.home_of = op_ra + op_rb
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

// 1. A coherent execution exists and is race-free.
run some_execution {
  openshmem_memory_model
  no_api_races
} for 0 but 16 Event expect 1

// 2. The backward outcome is ALLOWED when the reads are unordered (no fence):
//    r0==2 (ld_a reads st2) and r1==1 (ld_b reads st1).
run backward_outcome {
  openshmem_memory_model
  (st2 -> ld_a) in rf
  (st1 -> ld_b) in rf
} for 0 but 16 Event expect 1

// 3. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
