module memory_consistency/llvm/openshmem_predicates

// OpenSHMEM API-level memory model over the repo's LLVM memory model.
//
// The OpenSHMEM specification defines its API-level model by taking a PL-level
// model's axioms and "updating them to use api_hb rather than hb" (plus PEs and
// the API-level relations). This module does exactly that for the repo's LLVM
// memory model: it reinstates the full LLVM axiom set -- happens-before,
// monotonic (relaxed/unordered) coherence, and sequential consistency -- with
// every occurrence of llvm_hb replaced by api_hb, and per-(addr,PE) locations
// coming from same_location (constrained in openshmem_events.als).
//
// This is the LLVM analog of openshmem_predicates_c11.als, which instead
// transcribes the spec's simplified C++ axioms. The shared API-level relations,
// api_hb, api_may_see, api_happens_before, and no_api_races live in
// openshmem_relations.als; this module reuses them and adds the LLVM-specific
// monotonic and seqcst axioms retargeted to api_hb.

open memory_consistency/llvm/events
open memory_consistency/llvm/memory
open memory_consistency/llvm/memory_ordering
open memory_consistency/llvm/llvm_predicates
open memory_consistency/llvm/scopes
open memory_consistency/llvm/openshmem_events
open memory_consistency/llvm/openshmem_relations
open memory_consistency/llvm/utils

open util/relation

// =============================================================================
// Monotonic (aka C++ "relaxed") atomics -- llvm_monotonic_impl retargeted to
// api_hb.
// =============================================================================

pred api_monotonic_impl {
  // The modification order only relates monotonic modifications to the same
  // location.
  mo in Monotonic -> Monotonic

  // Writes with compatible scopes to the same location are mo-ordered.
  acyclic[mo, Monotonic]
  (Write & Monotonic) <: ((same_location - iden) & compatible_scope) :> (Write & Monotonic) in mo + ~mo

  // Modification orders are compatible with api happens-before.
  no mo & ~api_hb

  // If one atomic read api_hb-before another atomic read of the same address and
  // both are at least monotonic, the later read must not see an earlier value in
  // the address's modification order.
  all disj e1, e2 : Read & Monotonic |
    (e1 -> e2) in (api_hb & same_location & compatible_scope) => (
      some (e1 + e2) & DataRaceRead or
      (rf.e1 + rf.e2) not in Monotonic or
      (rf.e2 -> rf.e1) not in mo
    )

  // An RMW that reads from a monotonic access reads the one immediately before
  // it in the modification order.
  all E : RMW | (some (Monotonic & rf.E) => (rf.E in mo_imm.E))
}

// =============================================================================
// Sequential consistency -- llvm_seqcst_impl retargeted to api_hb.
// =============================================================================

// api_hb analog of llvm_strongly_hb (intro.races.8), with api_hb in the
// sequenced-before / happens-before composition.
fun api_strongly_hb : Event -> Event {
  ^(po + (SeqCst <: llvm_sw :> SeqCst) + po.api_hb.po) + initializes_before
}

pred api_seqcst_impl {
  seqcst_order = ^seqcst_order
  acyclic[seqcst_order, SeqCst]

  // SeqCst events with compatible scopes are totally ordered by seqcst_order.
  SeqCst <: (compatible_scope - iden) :> SeqCst in seqcst_order + ~seqcst_order

  // atomics.order.4, first clause: strongly-hb SeqCst pairs precede in S.
  SeqCst <: api_strongly_hb :> SeqCst in seqcst_order

  // atomics.order.4, remaining clauses: coherence-ordered SeqCst pairs (possibly
  // through SeqCst fences reached via api_hb) precede in S.
  SeqCst <: (maybe[(SeqCst & Fence) <: (api_hb & compatible_scope)]).
      (llvm_coherence_order & compatible_scope).
      (maybe[(api_hb & compatible_scope) :> (SeqCst & Fence)]) :> SeqCst in seqcst_order
}

// =============================================================================
// Top-level model
// =============================================================================

// The OpenSHMEM API-level memory model (LLVM flavor). Scopes are not exposed at
// the API level (spec: Compatibility with a Scoped Memory Model), so all scopes
// are compatible.
//
// Note: llvm_coherence_order / the RMW-atomicity rule above cover PL-level RMWs;
// extending RMW atomicity to OpenSHMEM AMO observable read/write pairs (the
// sb^amo_op axiom of api_mem_model.tex) is left as future work, as in the
// c11 module.
pred openshmem_memory_model {
  api_happens_before
  api_monotonic_impl
  api_seqcst_impl
  all_scopes_compatible
}
