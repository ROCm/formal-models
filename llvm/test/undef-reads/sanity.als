// RUN: %alstest -t %t %s

module memory_consistency/llvm/test/undef_reads/sanity
open memory_consistency/llvm/all_predicates


// Non-atomic events or non-compatible scopes are needed to get a data race.
run no_race_without_nonatomic_noncompatible {
  llvm_memory_model
  only_atomics
  only_compatible_scopes
  not no_races
} for 4 expect 0

// You can't have races with just a single thread.
run no_race_singlethread {
  llvm_memory_model
  num_threads = 1
  not no_races
} for 4 expect 0

run races_can_happen {
  llvm_memory_model
  not no_races
} for 4 expect 1

// Data races can happen without non-atomic events if there are non-compatible
// scopes.
run races_without_nonatomic {
  llvm_memory_model
  only_atomics
  not no_races
} for 4 expect 1

// Data races can happen without non-compatible scopes if there are non-atomic
// events.
run races_without_noncompatible {
  llvm_memory_model
  only_compatible_scopes
  not no_races
} for 4 expect 1
