# Memory Model for LLVM IR

This directory contains an experimental [Alloy](https://alloytools.org/) formalization of the memory consistency model of LLVM IR.
**This is an experimental academic project, not an authoritative definition of LLVM's semantics or the behavior of AMDGPU hardware.**

See the general [README](../README.md) for setup and basic usage instructions.

## Basic LLVM IR Model

The model formalizes the [memory model for concurrent operations](https://llvm.org/docs/LangRef.html#memory-model-for-concurrent-operations) and the [atomic memory ordering constraints](https://llvm.org/docs/LangRef.html#atomic-memory-ordering-constraints) from the LLVM Language Reference axiomatically.

The core of the model is the `llvm_memory_model` predicate defined in [llvm_predicates.als](./llvm_predicates.als).
It contains the constraints that a candidate program execution must satisfy to be a legal program execution.

A (candidate) program execution is modeled as a set of `Event` atoms (see [events.als](./events.als)) that are connected by the program order relation (the immediate successor relation `po_imm` and its transitive closure `po`).
Two different events are program-ordered iff they are in the same thread of execution; program order is total among the events of each thread.

`Event` atoms must be one of `SimpleRead`, `SimpleWrite`, `RMW` ("read, modify, write"), and `Fence`.
An `Event` that is `SimpleRead`, `SimpleWrite`, or `RMW` is also an `Access`; every `SimpleRead` or `RMW` is also a `Read`; every `SimpleWrite` or `RMW` is also a `Write` (see [memory.als](./memory.als)).
The accessed memory location is not represented explicitly in the Alloy model, there is only a `same_location` relation relating every `Access` to the same location.
Every location has an `Init` `SimpleWrite` that happens before any other `Event`.

Any `Event` can be `Atomic` (`Fence` and `RMW` must be).
They can additionally be `Monotonic`, `Release`, `Acquire`, and/or `SeqCst`; `Atomic` with none of these present represents the `unordered` memory ordering.
Constraints regarding which `Event` can/must have which orderings are in [memory_ordering.als](./memory_ordering.als).
Atomics are related by `compatible_scope` iff their `syncscope` and their position in the thread hierarchy allow them to synchronize and act atomically with respect to each other.

The central relations among events are:
- `rf`, the "reads-from" relation, connects writes to the reads that read from them. `rf` edges are in data flow direction, i.e., `write -> read`.
- `mo`, the monotonic modification order, connects `Monotonic` writes if they access the same location and they have compatible scopes.
- `seqcst_order`, the order among sequentially consistent operations, connects `SeqCst` events if they have compatible scopes.
- `llvm_hb` represents the "happens-before" partial order.

Their interactions are defined in predicates in [llvm_predicates.als](./llvm_predicates.als).

The property that makes the LLVM IR memory model unique is that data races are not immediate undefined behavior: racing reads return `undef`.
In the model, such reads are represented as `DataRaceRead`; they don't read from any `Write`.

Threads of execution are grouped into a tree-shaped hierarchy with `ScopeInstance` nodes (see [scopes.als](./scopes.als)).
In the basic LLVM IR model, the depth and structure of the `ScopeInstance` hierarchy, as well as what is required for atomics to have compatible scopes is only weakly constrained since this is a target-specific property.
For use in a traditional CPU setting, [llvm_predicates.als](./llvm_predicates.als) provides extensions to the `llvm_memory_model` predicate that further constrain the scopes:
- `llvm_memory_model_all_scopes_compatible` asserts that all atomics have compatible scopes; the scope hierarchy becomes irrelevant.
- `llvm_memory_model_flat_with_scope_inclusion` restricts the scope instances to a flat hierarchy: One system scope and arbitrarily many thread scopes that are right below the system scope.
  It also defines that two atomics have compatible scopes iff they have inclusive scope: either's syncscope instance includes the scope instance of the other's thread.

### Limitations

This model only covers selected aspects of the LLVM IR semantics.
The following aspects are not covered:
- types and values: We don't care which value is read, only which store wrote it.
- control flow: The model only imposes constraints on straight-line execution traces, control flow needs to be resolved before-hand.
- aliasing: Memory addresses are either known to be the same or they don't alias.
- uninitialized memory: Every memory location is assumed to be initialized by an atomic write that happens before any thread accesses it.
- mixed-size, misaligned, or partially overlapping accesses: Memory access granularity is per-location, not per-byte. Only perfectly overlapping or completely disjoint accesses are representable.
- infinite executions and liveness properties: Only finite numbers of events are supported, therefore liveness properties like this cannot be represented: "If an address is written monotonically by one thread, and other threads monotonically read that address repeatedly, the other threads must eventually see the write."

Moreover, the Alloy analyzer explores instances by translating the constraints into a SAT formula.
Expect reasonable performance for litmus tests with a handful of threads and accesses; scenarios with dozens of events will likely be slow or infeasible.

## AMDGPU Extensions

The AMDGPU model in [amdgpu_predicates.als](./amdgpu_predicates.als) extends the basic LLVM IR model with constraints that are AMDGPU-specific:
- Two atomics have compatible scopes iff they have inclusive scope: either's syncscope instance includes the scope instance of the other's thread.
- The scope instance hierarchy can be at most 6 levels deep (system, agent, cluster, workgroup, wavefront, singlethread).
  The Alloy model does not enforce that all of these levels are used; if the Alloy analyzer finds an instance where some or all of the threads are under fewer levels of scope hierarchy (e.g., a thread would execute directly under an agent scope), the instance can straightforwardly be extended to a full scope hierarchy by adding sufficiently long chains of scope instances.

### Missing Constructs

Some AMDGPU-specific constructs are not (yet) represented in the model:

- per-address spaces synchronization via `one-as` syncscopes or MMRAs
- the [availability and visibility](https://llvm.org/docs/AMDGPUMemoryModel.html) extension
- other intrinsics that access memory or otherwise affect the memory model
