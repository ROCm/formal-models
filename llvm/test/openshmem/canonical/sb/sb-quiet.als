module memory_consistency/llvm/test/openshmem/canonical/sb/sb_quiet

// SB with a shmem_quiet inserted between each thread's store and load. The stores
// and loads are plain (atomic) accesses; the quiet is an OpenSHMEM QuietOp. This
// is the quiet counterpart of sb-normal-fence.als (which used a seq_cst fence),
// and it exercises the quiet-based sequential-consistency axiom (api_quiet_sc)
// that is folded into the LLVM-flavored OpenSHMEM model (openshmem_predicates).
//
//   P0: x = 1 (atomic) ; shmem_quiet() ; r0 = y (atomic)
//   P1: y = 1 (atomic) ; shmem_quiet() ; r1 = x (atomic)
//   Weak (non-SC) outcome: r0 == 0 && r1 == 0
//
// All accesses are atomic, so there is never a data race. Results:
//   * Under the C11 api model (no SC axiom) the weak outcome is ALLOWED.
//   * Under the LLVM api model WITHOUT api_quiet_sc it is STILL allowed: total mo
//     (api_monotonic_impl) and SC-over-fences (api_seqcst_impl) are present, but a
//     quiet is not a seq_cst fence, so nothing forbids the reordering. (This
//     isolates that api_quiet_sc -- not total mo -- does the work.)
//   * Under the full LLVM api model (openshmem_memory_model, which now includes
//     api_quiet_sc) the weak outcome is FORBIDDEN: the quiet-SC axiom brackets the
//     coherence-order steps between the two quiets
//     (Q1 --api_hb--> ld_x --coh--> st_x --api_hb--> Q0, and symmetrically via y),
//     inducing Q1 before Q0 and Q0 before Q1 -> a cycle -> unsatisfiable.

open memory_consistency/llvm/openshmem_predicates          // LLVM api model (with api_quiet_sc)
open memory_consistency/llvm/openshmem_predicates_c11      // C11 api model (for the contrast)

// Two threads as two PEs (x on T0, y on T1).
one sig T0, T1 extends PE {}

one sig op_Q0, op_Q1 extends Operation {}   // the two shmem_quiet ops

one sig st_x extends SimpleWrite {}   // P0: x = 1 (atomic)
one sig ld_y extends SimpleRead  {}   // P0: r0 = y (atomic)
one sig st_y extends SimpleWrite {}   // P1: y = 1 (atomic)
one sig ld_x extends SimpleRead  {}   // P1: r1 = x (atomic)

one sig Init_x extends Init {}
one sig Init_y extends Init {}

fact program {
  po_imm = st_x -> op_Q0 + op_Q0 -> ld_y     // P0
         + st_y -> op_Q1 + op_Q1 -> ld_x     // P1

  no issues     // quiets issue no observable accesses; stores/loads are plain atomics
  no op_sb

  QuietOp = op_Q0 + op_Q1
  no PutOp and no GetOp and no AmoOp and no FenceOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  T0.target_of = st_x + ld_x + Init_x
  T1.target_of = st_y + ld_y + Init_y

  T0.home_of = st_x + op_Q0 + ld_y + Init_x
  T1.home_of = st_y + op_Q1 + ld_x + Init_y

  same_location =
      (Init_x + st_x + ld_x) -> (Init_x + st_x + ld_x) +
      (Init_y + st_y + ld_y) -> (Init_y + st_y + ld_y)
}

fact atomicity {
  st_x + ld_y + st_y + ld_x in Monotonic
  no (st_x + ld_y + st_y + ld_x) & (Release + Acquire)
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 0. Sanity: the LLVM api model has some legal execution of this program.
run some_execution {
  openshmem_predicates/openshmem_memory_model
} for 0 but 16 Event expect 1

// 1. C11 api model: the weak outcome is ALLOWED (no SC axiom).
run weak_outcome_c11 {
  openshmem_predicates_c11/openshmem_memory_model
  (Init_x -> ld_x) in rf
  (Init_y -> ld_y) in rf
} for 0 but 16 Event expect 1

// 2. LLVM api model WITHOUT api_quiet_sc: still ALLOWED (total mo + sc-over-fences
//    present, but a quiet is not a seq_cst fence). Isolates that api_quiet_sc does
//    the work, not total mo.
run weak_outcome_llvm_no_quiet_sc {
  api_happens_before
  api_monotonic_impl
  api_seqcst_impl
  all_scopes_compatible
  (Init_x -> ld_x) in rf
  (Init_y -> ld_y) in rf
} for 0 but 16 Event expect 1

// 3. Full LLVM api model (includes api_quiet_sc): the weak outcome is FORBIDDEN.
run weak_outcome_quiet_sc {
  openshmem_predicates/openshmem_memory_model
  (Init_x -> ld_x) in rf
  (Init_y -> ld_y) in rf
} for 0 but 16 Event expect 0

// 4. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_predicates/openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
