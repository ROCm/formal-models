// RUN: %alstest -t %t %s

module memory_consistency/llvm/test/general_properties/no_races_hb
open memory_consistency/llvm/all_predicates

fact {
  llvm_monotonic_impl
}

// This alternative to llvm_happens_before entails that Reads read from a Write
// that they can read from according to happens-before.
// Data races are ignored: Effectively, non-atomic accesses behave as unordered
// atomics.
pred no_races_happens_before {
  rf in llvm_may_see
  no DataRaceRead
}

// Some executions are possible with llvm_happens_before but not with
// no_races_happens_before.
run {
  llvm_happens_before and not no_races_happens_before
} for 6 expect 1

// Some executions are possible with no_races_happens_before but not with
// llvm_happens_before.
run {
  not llvm_happens_before and no_races_happens_before
} for 6 expect 1


// You can have executions without races in llvm_happens_before.
run {
  llvm_happens_before and no_races
} for 6 expect 1

// You can have executions without races in no_races_happens_before.
run {
  no_races_happens_before and no_races
} for 6 expect 1

// You can't have executions with races in no_races_happens_before.
run {
  no_races_happens_before and not no_races
} for 6 expect 0


// The happens-before implementations only differ if there are races.
run {
  llvm_happens_before and no_races and not no_races_happens_before
} for 6 expect 0


// The happens-before implementations only differ if there are non-atomics or
// non-compatible scopes.
run {
  llvm_happens_before and only_atomics and only_compatible_scopes and not no_races_happens_before
} for 6 expect 0
