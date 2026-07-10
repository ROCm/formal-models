// RUN: %alstest -t %t %s

module memory_consistency/llvm/test/ordering_monotonic/general_properties
open memory_consistency/llvm/all_predicates


run check_hb_implies_mo {
  llvm_memory_model

  // If two monotonic writes to the same location with compatible scope are in
  // happens-before, they are also in the modification order.
  some disj A, B : Monotonic & Write | (A -> B) in llvm_hb & same_location & compatible_scope
                                       and (A -> B) not in mo
} for 20 but 4 ScopeInstance, 4 Init expect 0

run check_hb_does_not_imply_mo_without_compatible_scopes {
  llvm_memory_model

  // We can't drop the compatible scope requirement from the above property.
  some disj A, B : Monotonic & Write | (A -> B) in llvm_hb & same_location
                                       and (A -> B) not in mo
} for 10 but 2 ScopeInstance, 4 Init expect 1

run check_mo_starts_with_init {
  llvm_memory_model

  // A monotonic write has no predecessor in the modification order iff it is an
  // Init write.

  (Write & Monotonic) - (Write & Monotonic).mo != Init
} for 10 but 4 ScopeInstance, 4 Init expect 0

