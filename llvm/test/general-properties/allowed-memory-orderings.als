// RUN: %alstest -t %t %s

module memory_consistency/llvm/test/general_properties/allowed_memory_orderings
open memory_consistency/llvm/all_predicates

// Validate that all Events can have appropriate memory orderings.

fun PlainRead : set Event {
  (Read - Write)
}

fun PlainWrite : set Event {
  (Write - Read)
}

// These run commands need the at least 2 atoms: one Init and one for the actual
// event.

run read_can_be_nonatomic {
  some PlainRead - Atomic
} for 2 expect 1

run write_can_be_nonatomic {
  some PlainWrite - Atomic
} for 2 expect 1


run read_can_be_atomic {
  some PlainRead & (Atomic - Monotonic)
} for 2 expect 1

run write_can_be_atomic {
  some PlainWrite & (Atomic - Monotonic)
} for 2 expect 1


run read_can_be_monotonic {
  some PlainRead & (Monotonic - (Release + Acquire))
} for 2 expect 1

run write_can_be_monotonic {
  some PlainWrite & (Monotonic - (Release + Acquire))
} for 2 expect 1


run read_cannot_release {
  some PlainRead & Release
} for 2 expect 0

run write_can_release {
  some PlainWrite & (Release - SeqCst)
} for 2 expect 1


run read_can_acquire {
  some PlainRead & (Acquire - SeqCst)
} for 2 expect 1

run write_cannot_acquire {
  some PlainWrite & Acquire
} for 2 expect 0


run fence_must_be_release_or_acquire {
  some Fence - (Acquire + Release)
} for 2 expect 0

run fence_can_be_release {
  some Fence & (Release - Acquire)
} for 2 expect 1

run fence_can_be_acquire {
  some Fence & (Acquire - Release)
} for 2 expect 1

run fence_can_be_acq_rel {
  some Fence & ((Acquire & Release) - SeqCst)
} for 2 expect 1


run write_can_be_seqcst {
  some PlainWrite & SeqCst
} for 2 expect 1

run read_can_be_seqcst {
  some PlainRead & SeqCst
} for 2 expect 1

run rmw_can_be_seqcst {
  some Read & Write & SeqCst
} for 2 expect 1

run fence_can_be_seqcst {
  some Fence & SeqCst
} for 2 expect 1

run rmw_at_least_monotonic {
  RMW not in Monotonic
} for 2 expect 0

run rmw_can_be_monotonic {
  some RMW & (Monotonic - (Acquire + Release))
} for 2 expect 1

run rmw_can_be_acquire {
  some RMW & (Acquire - Release)
} for 2 expect 1

run rmw_can_be_release {
  some RMW & (Release - Acquire)
} for 2 expect 1

run rmw_can_be_acqrel {
  some RMW & (Acquire & Release)
} for 2 expect 1
