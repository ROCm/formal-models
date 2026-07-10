module memory_consistency/llvm/amdgpu_model

// This Alloy module encodes the LLVM memory model with AMDGPU extensions. A
// finite execution is valid according to the LLVM memory model with AMDGPU
// extensions iff it corresponds to an Alloy instance for this module.

open memory_consistency/llvm/amdgpu_predicates

fact {
  amdgpu_memory_model
}
