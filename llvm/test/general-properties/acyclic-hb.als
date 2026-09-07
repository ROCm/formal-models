// RUN: %alstest -t %t %s

module memory_consistency/llvm/test/general_properties/acyclic_hb
open memory_consistency/llvm/all_predicates

open util/relation

// The monotonic coherence rules ensure that synchronizes-with edges can't form
// in a way that would make happens-before cyclic.
run {
  llvm_coherent_reads_from[llvm_hb]
  llvm_monotonic_impl[llvm_hb]

  not acyclic[llvm_hb, Event]
} for 6 expect 0

