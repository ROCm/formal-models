module memory_consistency/llvm/llvm_predicates

// This module provides the core predicates that constitute the LLVM IR memory
// model.

open memory_consistency/llvm/events
open memory_consistency/llvm/memory
open memory_consistency/llvm/memory_ordering
open memory_consistency/llvm/general_predicates
open memory_consistency/llvm/scopes
open memory_consistency/llvm/utils

open util/relation

// =============================================================================
// Top-level predicates
// =============================================================================

// Summary predicate collecting all the predicates that together implement the
// vanilla LLVM memory model. The target-specific scope hierarchy and scope
// compatibility are left unconstrained.
pred llvm_memory_model {
  llvm_coherent_reads_from[llvm_hb]
  llvm_monotonic_impl[llvm_hb]
  llvm_seqcst_impl[llvm_hb]
}

// A variant of the LLVM memory model where all scopes are compatible with each
// other, i.e., scope compatibility does not play any role.
pred llvm_memory_model_all_scopes_compatible {
  llvm_memory_model
  all_scopes_compatible
}

// A variant of the LLVM memory model with a flat (system, singlethread) scope
// hierarchy, where scope compatibility is scope inclusion.
pred llvm_memory_model_flat_with_scope_inclusion {
  llvm_memory_model
  scope_inclusion_is_scope_compatibility
  flat_scope_hierarchy
}

// =============================================================================
// Happens-before and data races
// =============================================================================

// Happens-before is the transitive closure of the union of program order and
// synchronizes-with. Moreover, initialization events happen before all other
// events.
fun llvm_hb : Event -> Event { ^(po_imm + llvm_sw) + initializes_before }

// Connects Reads to all Writes that they could read from without violating
// the provided happens-before relation.
fun llvm_may_see[hb: Event -> Event] : Write -> Read {
  // Reads can't read from Writes that have been overwritten, from writes that
  // happen after them, or from themselves.
  (Write <: same_location :> Read) - (write_between[hb] + ~hb + iden)
}

// This predicate entails that Reads read from a Write that they can read from
// according to the provided happens-before relation, unless they are part of a
// data race (in which case they read undef).
pred llvm_coherent_reads_from[hb: Event -> Event] {
  // This constraint is load-bearing: sw edges must follow rf edges, and hb is
  // what makes rf obey causality, so we need this additional fact to ensure hb
  // is a partial order.
  acyclic[hb, Event]

  rf in llvm_may_see[hb]

  // If a Read may read from more than one candidate (including the initial
  // value) and at least one of the involved accesses is not Atomic, we have a
  // data race and the Read reads undef.
  // If any pair of involved accesses has incompatible scopes, we also have a
  // data race.
  all R : Read | R in DataRaceRead iff (
      let involved_accs = R + (llvm_may_see[hb]).R |
        (involved_accs not in Atomic or (involved_accs -> involved_accs) not in compatible_scope) and
          (#(llvm_may_see[hb]).R >= 2)
    )
}

// =============================================================================
// Release/acquire synchronization
// =============================================================================

// Relates two events if they are connected by a release sequence.
fun llvm_release_seq : Write -> Read {
  // A Write W and a Read R are connected by a release sequence if R reads from
  // W or if there are RMWs connected via rf that connect W to R (C++20).
  // rf only connects Writes with Reads, so if there is an ^rf chain between two
  // Events, all intermediate Events must be RMWs.
  ^rf
}

// Connects Releases and Acquires that synchronize with each other according to
// the LLVM memory model.
fun llvm_sw : Release -> Acquire {
  Release <: ((maybe[llvm_fence_release_pairs]).llvm_release_seq.(maybe[llvm_fence_acquire_pairs]) & (compatible_scope - iden)) :> Acquire
  // For fences, only the syncscope of the fence itself matters, not that of the
  // paired access(es).
}

// Connects release Fences with the Writes that they pair with.
fun llvm_fence_release_pairs : Fence -> Write {
  (Fence & Release) <: po :> (Write & Atomic)
}

// Connects acquire Fences with the Reads that they pair with.
fun llvm_fence_acquire_pairs : Read -> Fence {
  (Read & Atomic) <: po :> (Fence & Acquire)
}

// =============================================================================
// Monotonic (aka C++ "relaxed") atomics
// =============================================================================

pred llvm_monotonic_impl[hb: Event -> Event] {
  // The modification order only relates monotonic modifications to the same
  // location.
  mo in Monotonic -> Monotonic

  // The modification order for a location is only a total order if all
  // monotonic writes have compatible scopes. Writes with incompatible scopes do
  // not need to be ordered (but they can be and need to be in some cases, when
  // compatible_scope is not transitive).
  acyclic[mo, Monotonic]
  (Write & Monotonic) <: ((same_location - iden) & compatible_scope) :> (Write & Monotonic) in mo + ~mo

  // Modification orders are compatible with happens-before.
  no mo & ~hb

  // A monotonic read R doesn't read from a monotonic write W2 if W2 is
  // modification-ordered after a monotonic write W1 that happens-after R.
  // This enforces C++'s read-write coherence rule:
  //   https://eel.is/c++draft/basic.exec#intro.races-13
  no hb.mo.rf & (iden :> (Read & Monotonic))

  // A monotonic read R doesn't read from a monotonic write W1 if there is
  // another monotonic write W2 that is modification-ordered after W1 and
  // happens-before R.
  // This enforces C++'s write-read coherence rule:
  //   https://eel.is/c++draft/basic.exec#intro.races-14
  no ~rf.mo.hb & (iden :> (Read & Monotonic))

  // "If one atomic read happens before another atomic read of the same address
  // and both are at least monotonic, the later read must not see an earlier
  // value in the address's modification order."
  all disj e1, e2 : Read & Monotonic |
    (e1 -> e2) in (hb & same_location & compatible_scope) => (
      some (e1 + e2) & DataRaceRead or // If one of them is part of a data race, there is no constraint.
      (rf.e1 + rf.e2) not in Monotonic or // If one of the reads is not from a monotonic write, there is no constraint.
      (rf.e2 -> rf.e1) not in mo
    )

  // The LangRef also says: "If an address is written monotonic-ally by one
  // thread, and other threads monotonic-ally read that address repeatedly, the
  // other threads must eventually see the write." We can't encode this liveness
  // property with our finite traces.

  // If an RMW (which needs to be at least monotonic, as asserted in
  // memory_ordering.als) reads from a monotonic access, it's (the) one before
  // it in the modification order.
  all E : RMW | (some (Monotonic & rf.E) => (rf.E in mo_imm.E))
}

// =============================================================================
// Sequential consistency
// =============================================================================

// C++ Standard, atomics.order.3 (https://eel.is/c++draft/atomics.order#3):
// "An atomic operation A on some atomic object M is coherence-ordered before
// another atomic operation B on M if
// - A is a modification, and B reads the value stored by A, or
// - A precedes B in the modification order of M, or
// - A and B are not the same atomic read-modify-write operation, and there
//   exists an atomic modification X of M such that A reads the value stored by X
//   and X precedes B in the modification order of M, or
// - there exists an atomic modification X of M such that A is coherence-ordered
//   before X and X is coherence-ordered before B."
fun llvm_coherence_order : Atomic -> Atomic {
  Atomic <: ^((rf + mo + ~rf.mo) - iden) :> Atomic
}

// C++ Standard, intro.races.8 (https://eel.is/c++draft/intro.races#8):
// "An evaluation A strongly happens before an evaluation D if, either
// - A is sequenced before D, or
// - A synchronizes with D, and both A and D are sequentially consistent atomic
//   operations ([atomics.order]), or
// - there are evaluations B and C such that A is sequenced before B, B happens
//   before C, and C is sequenced before D, or
// - there is an evaluation B such that A strongly happens before B, and B
//   strongly happens before D."
fun llvm_strongly_hb[hb: Event -> Event] : Event -> Event {
  ^(po + (SeqCst <: llvm_sw :> SeqCst) + po.hb.po) + initializes_before
}

pred llvm_seqcst_impl[hb: Event -> Event] {
  seqcst_order = ^seqcst_order
  acyclic[seqcst_order, SeqCst]

  // If two SeqCst events have compatible scopes, they must be ordered.
  // This is a relaxation of "totalOrder[seqcst_order, SeqCst]".
  SeqCst <: (compatible_scope - iden) :> SeqCst in seqcst_order + ~seqcst_order

  // From the C++ Standard, atomics.order.4 (https://eel.is/c++draft/atomics.order#4):
  // "First, if A and B are memory_order::seq_cst operations and A strongly
  // happens before B, then A precedes B in S."
  SeqCst <: llvm_strongly_hb[hb] :> SeqCst in seqcst_order

  // "Second, for every pair of atomic operations A and B on an object M, where
  // A is coherence-ordered before B, the following four conditions are required
  // to be satisfied by S:
  // - if A and B are both memory_order::seq_cst operations, then A precedes B
  //   in S; and
  // - if A is a memory_order::seq_cst operation and B happens before a
  //   memory_order::seq_cst fence Y, then A precedes Y in S; and
  // - if a memory_order::seq_cst fence X happens before A and B is a
  //   memory_order::seq_cst operation, then X precedes B in S; and
  // - if a memory_order::seq_cst fence X happens before A and B happens before
  //   a memory_order::seq_cst fence Y, then X precedes Y in S."
  SeqCst <: (maybe[(SeqCst & Fence) <: (hb & compatible_scope)]).
      (llvm_coherence_order & compatible_scope).
      (maybe[(hb & compatible_scope) :> (SeqCst & Fence)]) :> SeqCst in seqcst_order
  // Note: compatible_scope only relates Atomic Events, so we don't need to
  //       restrict to Atomic explicitly.
}

pred alternative_seqcst_impl[hb: Event -> Event] {
  // It's actually not necessary to explicitly represent the seqcst_order, we
  // can instead use this acyclicity constraint. This constraint is satisfied
  // iff a suitable total seqcst_order exists.
  // This is similar to what Batty et al. proposed in "Overhauling SC Atomics in
  // C11 and OpenCL".
  // Currently not used, left for reference.
  acyclic[
    (SeqCst <: llvm_strongly_hb[hb] :> SeqCst) +
    (SeqCst <: (maybe[(SeqCst & Fence) <: (hb & compatible_scope)]).
        (llvm_coherence_order & compatible_scope).
        (maybe[(hb & compatible_scope) :> (SeqCst & Fence)]) :> SeqCst), SeqCst]
}
