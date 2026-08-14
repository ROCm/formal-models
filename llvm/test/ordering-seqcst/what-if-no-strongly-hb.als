// RUN: %alstest -t %t %s

module memory_consistency/llvm/test/ordering_seqcst/what_if_no_strongly_hb
open memory_consistency/llvm/all_predicates


pred no_strongly_hb_seqcst_impl {
  // same as llvm_seqcst_impl, but using llvm_hb instead of llvm_strongly_hb
  seqcst_order = ^seqcst_order
  acyclic[seqcst_order, SeqCst]
  SeqCst <: (compatible_scope - iden) :> SeqCst in seqcst_order + ~seqcst_order

  // This normally uses llvm_strongly_hb:
  SeqCst <: llvm_hb :> SeqCst in seqcst_order
  // SeqCst <: llvm_strongly_hb :> SeqCst in seqcst_order

  SeqCst <: (maybe[(SeqCst & Fence) <: (llvm_hb & compatible_scope)]).
      (llvm_coherence_order & compatible_scope).
      (maybe[(llvm_hb & compatible_scope) :> (SeqCst & Fence)]) :> SeqCst in seqcst_order
}


pred no_strongly_hb_memory_model {
  llvm_coherent_reads_from[llvm_hb]
  llvm_monotonic_impl[llvm_hb]
  no_strongly_hb_seqcst_impl

  scope_inclusion_is_scope_compatibility
  flat_scope_hierarchy
}

// There is an execution that is allowed by the constraints that use
// llvm_strongly_hb but not by the constraints that use llvm_hb instead.
run check_no_strongly_hb_stronger {
  llvm_memory_model
  not no_strongly_hb_memory_model

  no DataRaceRead
  no Atomic - Monotonic
  no Fence
  Event = Monotonic
} for 5 but 1 ScopeInstance expect 1

run check_no_strongly_hb_weaker {
  not llvm_memory_model
  no_strongly_hb_memory_model
} for 5 but 3 ScopeInstance expect 0

