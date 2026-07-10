// RUN: %alstest -t %t %s

module memory_consistency/llvm/test/syncscopes/basic
open memory_consistency/llvm/all_predicates
open memory_consistency/llvm/scopes


// The scope hierarchy cannot have cycles.
run check_no_scope_cycles {
  llvm_memory_model
  some disj s1, s2 : ScopeInstance | s1 in s2.*parent and s2 in s1.*parent
} for 6 expect 0

// No scope can have multiple parent scopes.
run check_scope_tree {
  llvm_memory_model
  some disj s1, s2, s3 : ScopeInstance | s2 in s1.parent and s3 in s1.parent
} for 6 expect 0

// Events can have compatible scopes.
run check_compatible_scope_possible {
  llvm_memory_model
  scope_inclusion_is_scope_compatibility
  some disj e1, e2 : Atomic | (e1 -> e2) in compatible_scope
} for 6 expect 1

// Events can have incompatible scopes.
run check_incompatible_scope_possible {
  llvm_memory_model
  scope_inclusion_is_scope_compatibility
  some disj e1, e2 : Atomic | (e1 -> e2) not in compatible_scope
} for 6 expect 1

// Events can have compatible but distinct scopes.
run check_compatible_distinct_scope_possible {
  llvm_memory_model
  scope_inclusion_is_scope_compatibility
  some disj e1, e2 : Atomic | (e1 -> e2) in compatible_scope and e1.syncscope_instance != e2.syncscope_instance
} for 6 expect 1

// Events with the same syncscope instance cannot have incompatible scopes.
run check_incompatible_same_scope {
  llvm_memory_model
  some disj e1, e2 : Atomic | (e1 -> e2) not in compatible_scope and e1.syncscope_instance = e2.syncscope_instance
} for 6 expect 0

// The same_thread relation is consistent with the execscope_instance relation.
run check_consistent_threads {
  llvm_memory_model
  some disj e1, e2 : Event - Init | (e1 -> e2) in same_thread and e1.execscope_instance != e2.execscope_instance
} for 6 expect 0

