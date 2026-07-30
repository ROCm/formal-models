module memory_consistency/llvm/test/openshmem/canonical/sb/sb_normal_fence

// SB realized with ONLY plain (atomic) memory accesses -- NO OpenSHMEM API calls,
// no operations, no observable accesses -- and a sequentially-consistent (SeqCst)
// fence between each thread's store and its load. This isolates the question:
// does a real memory fence forbid the weak SB outcome under the base LLVM model
// versus the (C11-flavored) OpenSHMEM API model?
//
//   P0: x = 1 (atomic) ; fence(seq_cst) ; r0 = y (atomic)
//   P1: y = 1 (atomic) ; fence(seq_cst) ; r1 = x (atomic)
//   Weak (non-SC) outcome: r0 == 0 && r1 == 0
//
// All accesses are atomic (Monotonic), so there is never a data race; the only
// question is whether the weak outcome is allowed.
//
// FINDING (see the two runs):
//   * Under the base LLVM model (llvm_memory_model) the weak outcome is FORBIDDEN.
//     The SeqCst fences feed the sequential-consistency axiom (atomics.order.4,
//     the sc-fence / coherence-order clause): F1 hb-before r1=x, x reads-before
//     x=1, x=1 hb-before F0  =>  F1 precedes F0 in the SC order S; symmetrically
//     via y, F0 precedes F1 in S. That is a cycle in seqcst_order, which is
//     required to be acyclic -- so the weak outcome is unsatisfiable.
//   * Under the OpenSHMEM API model (openshmem_predicates_c11) the weak outcome is
//     ALLOWED. That model transcribes only the spec's SIMPLIFIED C11 axioms
//     (acyclic api_hb + the coherence axiom) and intentionally OMITS sequential
//     consistency. A SeqCst fence there contributes only release/acquire-style
//     edges (llvm_sw), which need an rf release-sequence to synchronize across
//     threads; in the weak outcome both loads read the initial value, so no such
//     cross-thread edge exists and api_hb stays acyclic. With no SC axiom there is
//     nothing to forbid the store->load reordering.
//
// (The LLVM-based OpenSHMEM model, openshmem_predicates.als, would behave like the
// LLVM model here, since it reinstates the seqcst axiom over api_hb.)

open memory_consistency/llvm/openshmem_predicates_c11
open memory_consistency/llvm/openshmem_predicates

// Two threads, modeled as two PEs (needed only to satisfy the OpenSHMEM
// structural facts; the LLVM model ignores PEs). x lives on T0, y on T1.
one sig T0, T1 extends PE {}

one sig st_x extends SimpleWrite {}   // P0: x = 1 (atomic)
one sig ld_y extends SimpleRead  {}   // P0: r0 = y (atomic)
one sig st_y extends SimpleWrite {}   // P1: y = 1 (atomic)
one sig ld_x extends SimpleRead  {}   // P1: r1 = x (atomic)

one sig F0, F1 extends Fence {}       // seq_cst fences

one sig Init_x extends Init {}
one sig Init_y extends Init {}

fact program {
  po_imm = st_x -> F0 + F0 -> ld_y     // P0
         + st_y -> F1 + F1 -> ld_x     // P1

  // No OpenSHMEM operations in this test.
  no Operation
}

fact locations_and_pes {
  // Target PE of each access (x on T0, y on T1).
  T0.target_of = st_x + ld_x + Init_x
  T1.target_of = st_y + ld_y + Init_y

  // Home (issuing) thread of each event.
  T0.home_of = st_x + F0 + ld_y + Init_x
  T1.home_of = st_y + F1 + ld_x + Init_y

  same_location =
      (Init_x + st_x + ld_x) -> (Init_x + st_x + ld_x) +
      (Init_y + st_y + ld_y) -> (Init_y + st_y + ld_y)
}

fact atomicity {
  // Accesses are relaxed atomics; the fences are sequentially consistent.
  st_x + ld_y + st_y + ld_x in Monotonic
  no (st_x + ld_y + st_y + ld_x) & (Release + Acquire)
  F0 + F1 in SeqCst
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 0. Sanity: the program has some legal LLVM execution.
run some_llvm_execution {
  llvm_memory_model
  all_scopes_compatible
} for 0 but 16 Event expect 1

// 1. LLVM model: the weak (non-SC) outcome is FORBIDDEN by the seq_cst fences.
run weak_outcome_llvm {
  llvm_memory_model
  all_scopes_compatible
  (Init_x -> ld_x) in rf     // r1 = 0
  (Init_y -> ld_y) in rf     // r0 = 0
} for 0 but 16 Event expect 0

// 2. OpenSHMEM API model (C11 flavor): the weak outcome is ALLOWED (SC omitted).
run weak_outcome_api_c11 {
  openshmem_predicates_c11/openshmem_memory_model
  (Init_x -> ld_x) in rf
  (Init_y -> ld_y) in rf
} for 0 but 16 Event expect 1

// 3. OpenSHMEM API model (LLVM flavor): the weak outcome is FORBIDDEN. This model
//    reinstates the seqcst axiom over api_hb (api_seqcst_impl), so the seq_cst
//    fences forbid SB just as in the base LLVM model.
run weak_outcome_api_llvm {
  openshmem_predicates/openshmem_memory_model
  (Init_x -> ld_x) in rf
  (Init_y -> ld_y) in rf
} for 0 but 16 Event expect 0
