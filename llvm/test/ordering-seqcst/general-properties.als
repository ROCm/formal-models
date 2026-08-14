// RUN: %alstest -t %t %s

module memory_consistency/llvm/test/ordering_seqcst/general_properties
open memory_consistency/llvm/all_predicates

open util/relation


run check_all_compatible_scope_implies_total_order {
  llvm_memory_model

  only_compatible_scopes
  not totalOrder[*seqcst_order, SeqCst]
} for 2 but 4 ScopeInstance expect 0

run check_noncompatible_scope_allows_nontotal_order {
  llvm_memory_model

  not totalOrder[*seqcst_order, SeqCst]
} for 2 but 4 ScopeInstance expect 1

run check_coherence_order_acyclic {
  llvm_memory_model

  not acyclic[llvm_coherence_order, Atomic]
} for 6 but 3 ScopeInstance expect 0

run check_all_seqcst_rf_follows_seqcst_order {
  // The LLVM LangRef says this about sequentially-consistent reads:
  // "Each sequentially-consistent read sees the last preceding write to the
  // same address in this global order."
  // That only makes sense if all Events are SeqCst; this check validates that
  // it holds in this case.

  llvm_memory_model

  Event = SeqCst

  not rf in seqcst_order
} for 6 but 3 ScopeInstance expect 0

run check_all_seqcst_rf_does_not_skip_seqcst_writes {
  // The LLVM LangRef says this about sequentially-consistent reads:
  // "Each sequentially-consistent read sees the last preceding write to the
  // same address in this global order."
  // That only makes sense if all Events are SeqCst; this check validates that
  // it holds in this case.

  llvm_memory_model

  Event = SeqCst

  not (all r: Read | all w: Write |
    (w -> r) in rf implies ((w -> r) in seqcst_order and no w2: Write | (w -> w2) + (w2 -> r) in same_location & seqcst_order))

} for 6 but 3 ScopeInstance expect 0

run acyclic_coherence_order {
  llvm_memory_model

  some disj a, b: Event | (a -> b) + (b -> a) in llvm_coherence_order
} for 6 but 1 ScopeInstance expect 0


run implicit_order {
  llvm_memory_model

  not alternative_seqcst_impl[llvm_hb]

} for 6 but 3 ScopeInstance expect 0
