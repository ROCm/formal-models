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
//
// It also folds in the quiet-based sequential-consistency axiom (api_quiet_sc):
// shmem_quiet acts as a global SC ordering point, the api_hb / QuietOp analog of
// api_seqcst_impl's sc-fence clause. This relies on api_monotonic_impl's total mo
// (see the note there), so it does not need a separate mo-totality assumption.

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
// Quiet-based sequential consistency
// =============================================================================

// shmem_quiet as a sequentially-consistent ordering point -- the api_hb / QuietOp
// analog of the sc-fence clause in api_seqcst_impl. A coherence-order step
// bracketed between two shmem_quiet operations (each api_hb-related to the
// bracketed access) induces an order over quiets, which must be acyclic. This
// relies on the per-location total mo established by api_monotonic_impl (so the
// from-read step ~rf.mo of llvm_coherence_order exists); that is precisely why SB
// with a quiet between the store and the load is unsatisfiable here.
//
// Note: this treats every shmem_quiet as a GLOBAL SC point, which is stronger
// than OpenSHMEM's actual per-PE / point-to-point quiet-completion semantics.
pred api_quiet_sc {
  // Materialized total order over shmem_quiet operations, represented in the same
  // way llvm_seqcst_impl represents seqcst_order for SC fences: an explicit,
  // transitive, acyclic order (the quiet_order field on QuietOp) that is total and
  // contains the strongly-hb and coherence-bracketed pairs. Equivalent to the
  // acyclic formulation, but kept structurally symmetric with the base model.
  quiet_order = ^quiet_order
  acyclic[quiet_order, QuietOp]

  // All distinct quiets are totally ordered by quiet_order. (The base filters
  // SeqCst pairs by compatible_scope; quiets carry no scope, so every pair is
  // ordered.)
  (QuietOp -> QuietOp) - iden in quiet_order + ~quiet_order

  // atomics.order.4, first clause (analog): strongly-hb quiet pairs precede.
  QuietOp <: api_strongly_hb :> QuietOp in quiet_order

  // atomics.order.4, coherence clause (analog): a coherence-order step bracketed
  // between two quiets via api_hb precedes -- QuietOp in place of (SeqCst & Fence),
  // api_hb in place of llvm_hb. (The quiet brackets drop compatible_scope, since
  // quiets are not Atomic and carry no scope; the coherence step keeps it.)
  QuietOp <: (maybe[QuietOp <: api_hb]).
      (llvm_coherence_order & compatible_scope).
      (maybe[api_hb :> QuietOp]) :> QuietOp in quiet_order
}

// ---------------------------------------------------------------------------
// UNUSED alternative (kept for reference; commented out, NOT part of any model).
//
// A "cleaner" quiet-SC axiom that integrates shmem_quiet directly into the
// sequential-consistency machinery of api_seqcst_impl, instead of the standalone
// api_quiet_sc above. It treats each QuietOp as an additional SC fence, sharing
// one SC order with the SeqCst events. Structurally this mirrors api_seqcst_impl
// exactly -- the same strongly-hb clause and the same maybe[]-bracketed
// coherence-order clause -- so it inherits, for free, all four atomics.order.4
// sub-cases and the scope handling (things the narrower api_quiet_sc does not
// cover). Unlike the active api_quiet_sc -- which materializes a quiet_order field
// over QuietOp -- this integrated version uses the acyclic formulation
// (cf. alternative_seqcst_impl), because it ranges over the MIXED set
// sc_points = SeqCst + QuietOp, for which no single typed order field exists.
//
// WHY IT IS UNUSED: this version makes shmem_quiet interact with LLVM-level
// SeqCst fences -- they would share a single SC order and could bracket the same
// coherence step (e.g. a quiet on one side, a seq_cst fence on the other). That
// cross-interaction is intentionally NOT wanted for now, so the active model uses
// api_quiet_sc (which orders only quiets among themselves). Enable this only if
// quiet/fence interaction is later desired.
//
// pred api_seqcst_impl_with_quiet {
//   // Existing SeqCst constraints (as in api_seqcst_impl).
//   seqcst_order = ^seqcst_order
//   acyclic[seqcst_order, SeqCst]
//   SeqCst <: (compatible_scope - iden) :> SeqCst in seqcst_order + ~seqcst_order
//   SeqCst <: api_strongly_hb :> SeqCst in seqcst_order
//   SeqCst <: (maybe[(SeqCst & Fence) <: (api_hb & compatible_scope)]).
//       (llvm_coherence_order & compatible_scope).
//       (maybe[(api_hb & compatible_scope) :> (SeqCst & Fence)]) :> SeqCst in seqcst_order
//
//   // Quiets folded into the same SC order as SeqCst fences: sc_points are the
//   // ordered elements, sc_fences are the bracketing points.
//   let sc_points = SeqCst + QuietOp,
//       sc_fences = (SeqCst & Fence) + QuietOp |
//   acyclic[
//     (sc_points <: api_strongly_hb :> sc_points)
//     +
//     (sc_points <:
//        (maybe[sc_fences <: (api_hb & compatible_scope)]).
//        (llvm_coherence_order & compatible_scope).
//        (maybe[(api_hb & compatible_scope) :> sc_fences])
//      :> sc_points),
//     sc_points ]
// }
// ---------------------------------------------------------------------------

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
  api_quiet_sc
  all_scopes_compatible
}
