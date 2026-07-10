// RUN: %alstest -t %t %s

module memory_consistency/llvm/test/syncscopes/advanced_properties
open memory_consistency/llvm/all_predicates
open memory_consistency/llvm/scopes


// Atomic accesses with non-compatible scopes can cause data races.
run check_scoped_datarace_enough_scopes {
  llvm_memory_model

  only_atomics

  some DataRaceRead
} for 8 but 2 ScopeInstance expect 1

// A single scope (the System scope) is not enough for data races among Atomics.
run check_scoped_datarace_not_enough_scopes {
  llvm_memory_model

  only_atomics

  some DataRaceRead
} for 8 but 1 ScopeInstance expect 0

// Alternative definition of inclusive scope: a, b have inclusive scope if their syncscopes are both ancestors of their execscopes.
run syncscopes_common_ancestors_implies_inclusive_scope {
  llvm_memory_model
  scope_inclusion_is_scope_compatibility

  some disj a, b : Atomic - Init | ((a.syncscope_instance + b.syncscope_instance) in common_ancestors[a.execscope_instance, b.execscope_instance]) and (a -> b) not in inclusive_scope

} for 8 but 8 ScopeInstance expect 0


run no_escape_past_syncscope {
  llvm_memory_model
  scope_inclusion_is_scope_compatibility

  some disj a, b : Atomic - Init | a.syncscope_instance not in b.execscope_instance.*parent and (a -> b) in rf
  // Only synchronization via release/acquire allows data transfer between
  // instructions with non-inclusive scopes.
  no llvm_sw

} for 8 expect 0

run inclusive_scope_is_not_transitive {
  llvm_memory_model
  scope_inclusion_is_scope_compatibility

  // This constraint doesn't matter, but it simplifies the found counterexamples
  // (they only use fences this way).
  no Read + Write

  some disj a, b, c : Atomic |
      (a -> b) + (b -> c) in inclusive_scope and (a -> c) not in inclusive_scope
} for 3 but 2 ScopeInstance expect 1

