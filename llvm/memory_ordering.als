module memory_consistency/llvm/memory_ordering

// This module defines Fence events and the memory orderings.
//
// Memory orderings are properties of Events, they are represented via subset
// signatures. Stronger memory orderings imply weaker memory orderings: E.g., a
// Release or Acquire event must also be Monotonic.
// Atomics with no other memory ordering represent events with the
// 'unordered' memory ordering.

open memory_consistency/llvm/memory
open memory_consistency/llvm/events

// Represents the execution of a fence instruction.
sig Fence extends Event { }

sig Monotonic in Event { }

sig Release in Event { }

sig Acquire in Event { }

sig SeqCst in Event {
  // All direct or indirect successors in the sequentially consistent order.
  seqcst_order: set SeqCst
}

fact ordering_inclusions {
  Monotonic in Atomic
  Release + Acquire in Monotonic

  SeqCst in Release + Acquire
  SeqCst & Fence in Release & Acquire
  SeqCst & Read in Acquire
  SeqCst & Write in Release
}

fact ordering_requirements {
  // LLVM LangRef: Fences must be at least acquire or release.
  Fence in Acquire + Release

  // Non-RMW Reads cannot release.
  no Release & SimpleRead

  // Non-RMW Writes cannot acquire.
  no Acquire & SimpleWrite

  // RMWs must be at least monotonic.
  RMW in Monotonic

  // We consider initializations to be sequentially consistent accesses.
  Init in SeqCst
}
