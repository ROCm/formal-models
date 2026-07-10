module memory_consistency/llvm/llvm_model

// This Alloy module encodes the LLVM memory model. A finite execution is valid
// according to the LLVM memory model iff it corresponds to an Alloy instance
// for this module.

open memory_consistency/llvm/llvm_predicates

fact {
  llvm_memory_model
}
