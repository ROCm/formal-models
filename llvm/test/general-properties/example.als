// Instructions for the llvm-lit test harness:
// RUN: %alstest -t %t %s

// The path for this module, determines how imports are resolved. It should
// mirror the directory structure.
module memory_consistency/llvm/test/general_properties/example

// Import the module with all the predicates for the LLVM IR memory model.
open memory_consistency/llvm/all_predicates

// Try to find an execution with a data race that satisfies the
// llvm_memory_model and that has two threads.
run data_races_exist {
  llvm_memory_model
  num_threads = 2
  some DataRaceRead
} for 0 but 4 Event  // Consider executions with up to 4 Events of any kind.
  expect 1  // We expect such executions to exist, consider it an error if we find none.

// Try to find an execution with a data race that satisfies the
// llvm_memory_model and that has one thread.
run data_races_need_two_threads {
  llvm_memory_model
  num_threads = 1
  some DataRaceRead
} for 0 but 4 Event  // Consider executions with up to 4 Events of any kind.
  expect 0  // We expect such executions to not exist, consider it an error if we find at least one.
