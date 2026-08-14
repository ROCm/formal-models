module memory_consistency/llvm/amdgpu_predicates

// This module provides additional predicates besides those in
// llvm_predicates.als that constitute the LLVM IR memory model with AMDGPU
// extensions.

open memory_consistency/llvm/llvm_predicates
open memory_consistency/llvm/scopes

open util/relation

pred amdgpu_memory_model {
  llvm_coherent_reads_from[llvm_hb]
  llvm_monotonic_impl[llvm_hb]
  llvm_seqcst_impl[llvm_hb]

  scope_inclusion_is_scope_compatibility
  amdgpu_max_scope_depth
}

pred amdgpu_max_scope_depth {
  // For AMDGPU, the scope hierarchy is at most 6 levels deep (system, agent,
  // cluster, workgroup, wave, thread). Smaller bounds may be useful to speed up
  // solving.
  no ScopeInstance.parent.parent.parent.parent.parent.parent
}

