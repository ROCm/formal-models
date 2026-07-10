# Tests for Alloy Models

This project provides a domain-specific language to specify concrete test cases for analysis under Alloy models.
A test case specifies static aspects of multi-threaded program executions (which operations are executed, how they are arranged in threads, how the threads are arranged in the scopes) and checks if executions exist that satisfy these static aspects and additional properties.
The `gentest` python module converts these tests into Alloy signatures, facts, and commands and optionally runs the Alloy analyzer on the resulting module (see the general [README](../README.md) for its usage).

Program aspects that are not relevant to the model are omitted from the test case syntax.
For example, test cases for the LLVM IR memory model do not contain types, values, control flow, or language/library constructs to create threads of execution because these concepts are not represented in the Alloy model.

For a quick overview, consider the following [annotated example test](../llvm/test/example.test) for the LLVM IR memory model (the annotations are in line comments started by `//`):

```
// Test that the release-acquire handshake works:
#thread 0                          // The following operations belong to thread 0.
  $A: store p                      // a non-atomic store of some value to address 'p' (named $A for later reference)
  fence.release                    // a fence with release semantics
  $X: store.monotonic flag         // an atomic store with monotonic memory ordering to address 'flag' (named $X for later reference)

#thread 1                          // The following operations belong to thread 1.
  $Y: load.monotonic flag          // an atomic load with monotonic memory ordering from address 'flag' (named $Y for later reference)
  fence.acquire                    // a fence with acquire semantics
  $B: load p                       // a non-atomic load from address 'p' (named $B for later reference)

#push llvm_memory_model            // Establish that executions should satisfy the LLVM memory model predicate (defined in llvm/llvm_predicates.als).

#push ($X -> $Y) in rf             // Establish the assumption that the load $Y reads from the store $X for the following checks.

#check sat ($A -> $B) in rf        // Check that there is an execution where $B reads from $A.
#check unsat ($A -> $B) not in rf  // Check that there is no execution where $B does not read from $A.
                                   // (because the fences synchronize and establish a happens-before relation)

#pop                               // Remove the last pushed assumption: that $Y reads from $X.

#check sat ($A -> $B) not in rf    // Check that, now, there is an execution where $B does not read from $A.
                                   // (because the fences only synchronize if $Y reads from $X).
```

## Syntax

Each line of a test file can contain either:
* a `#` directive
* an instruction

Empty lines and comments are also allowed.

* Comments start with `//` and last through the whole line.
* Comments can take a whole line, or be at the end of an instruction or directive.

### Directives

Directives determine the context of the following instructions or affect what
properties are checked. The following kinds of directives are supported:

* `#<scope> <id>`, where `scope` is a model-specific scope/topology level (`thread` for the LLVM IR model, one of `[agent, cluster, workgroup, wave, thread]` for the AMDGPU model) and `id` is a string identifying a scope instance of that scope.
  The `id` may only contain alphanumeric characters and underscores; it must not start with an underscore.
    * Declares that the following instructions and lower-level scope directives belong to the scope instance with the given ID of the given scope.
    * Per level, `id`s must be unique (so, e.g., there cannot be two threads `0`, even if they are in different surrounding scope instances).
    * Tests can omit any number of leading scope directives.
      In that case, scope instances at the omitted levels are implicitly created with the same ID as their parent scope instance (or an error is raised if that is not possible).
    * Examples: `#workgroup 0`, `#wave B`, `#thread t1`
* `#check`
    * First argument is either `sat` or `unsat`
    * Optionally can be followed by some Alloy code to be pasted in the check.
      * The Alloy code can use substitutions such as `$foo` where `foo` is a named instruction.
    * Optionally can be followed by `for N1 Sig1 N2 Sig2 ...` to specify the scope (i.e., the number of atoms per signature) for the Alloy analyzer.
    * Examples:
      * `#check sat`
      * `#check unsat consistent_ordering`
      * `#check sat $A -> $B in sw for 2 ScopeInstance`
* `#assert <alloy-constraint>`
    * Equivalent to `#check unsat not (<alloy-constraint>)`
    * Optionally can be followed by `for N1 Sig1 N2 Sig2 ...` to specify the scope (i.e., the number of atoms per signature) for the Alloy analyzer.
    * Example: `#assert A => B` (equivalent to `#check unsat A and not B`)
* `#push <alloy-constraint>` 
    * Pushes an Alloy constraint onto the stack of constraints.
    * The constraint will be added to all following check and assert commands (via a logical conjunction/"and") until it is `#pop`ped off the stack again.
    * Examples:
      * `#push $A -> $B in rf`
      * `#push llvm_memory_model`
* `#pop [<N>]`
    * Pops the top `N` Alloy constraints from the stack of constraints.
    * If `N` is omitted, it defaults to 1.
    * Examples:
      * `#pop`
      * `#pop 2`

If no `#check` or `#assert` directive is present, an implicit `#check sat` is
inserted at the end of the file (with the state of the constraint stack at that
point).

### Instructions

Instructions follow this pattern:

* `[$name:] opcode(.attr)* [addr]`

`.attr` is an attribute of the instruction.
Allowed opcodes and attributes are model-specific.
The order of attributes does not matter.

Some instructions require an address `addr` (e.g., load and store), while others do not (e.g., fence).
Addresses are just strings (e.g., `p`, `flag`) and do not have to be declared beforehand.
If two addresses have different names, they do not alias.

Instructions can optionally be prefixed with `$name:` to set their name, for references in Alloy constraints in directives.

For example:
```
$X: store p
$Y: load p
#check sat ($X -> $Y) in rf
```

#### LLVM:

The following instruction opcodes are supported:

* `load`: Corresponds to the LLVM IR instruction of the same name.
* `store`: Corresponds to the LLVM IR instruction of the same name.
* `rmw`: Corresponds to LLVM's `atomicrmw` and `cmpxchg` (if successful) instructions.
* `fence`: Corresponds to the LLVM IR instruction of the same name.

The following attributes exist:
* memory ordering (corresponds to LLVM's memory orderings, no memory ordering means that the operation is non-atomic):
  * `unordered`
  * `monotonic`
  * `acquire`
  * `release`
  * `acq_rel`
  * `seq_cst`
* syncscope (can only be present if a memory ordering is present; no syncscope means `system` scope):
  * `ss=system`
  * `ss=singlethread` or `ss=thread` or `ss=st`

#### LLVM with AMDGPU extensions:
The same instructions and attributes as for LLVM are supported, with the following extensions:
* The supported syncscopes are:
  * `ss=system`
  * `ss=agent` or `ss=ag`
  * `ss=cluster` or `ss=cl`
  * `ss=workgroup` or `ss=wg`
  * `ss=wavefront` or `ss=wave` or `ss=wf`
  * `ss=singlethread` or `ss=thread` or `ss=st`


#### Example translations from LLVM IR to the test syntax

| LLVM IR instruction                                                | Test syntax                   |
|--------------------------------------------------------------------|-------------------------------|
| `store i32 1, ptr %p`                                              | `store p`                     |
| `store atomic i32 2, ptr %p monotonic, align 4`                    | `store.monotonic p`           |
| `store atomic i32 3, ptr %p syncscope("agent") release, align 4`   | `store.release.ss=agent p`    |
| `load i8, ptr %q`                                                  | `load q`                      |
| `load atomic i32, ptr %p acquire, align 4`                         | `load.acquire p`              |
| `load atomic i32, ptr %p syncscope("workgroup") seq_cst, align 4`  | `load.seq_cst.ss=workgroup p` |
| `fence release`                                                    | `fence.release`               |
| `fence syncscope("workgroup") seq_cst`                             | `fence.seq_cst.ss=workgroup`  |
| `atomicrmw add ptr %p, i32 1 monotonic`                            | `rmw.monotonic p`             |


## Recommended Testing Strategy

* In almost all cases, a test should include a `#push <relevant memory model predicate>` directive to specify the relevant memory model.
* Each test should have at least one `#check sat <...>` directive (potentially without additional constraints). This ensures that the test is not trivially unsatisfiable and that the model is consistent.
* If the test should validate that certain properties must hold (e.g., "B must read from A"), then this should be expressed as either `#check unsat <negation of property>` (e.g. `#check unsat $A -> $B not in rf`) or, equivalently, as `#assert <property>` (e.g. `#assert $A -> $B in rf`).

## Commonly used idioms in tests for the LLVM IR model

### "A synchronizes with B"

The considered subset of LLVM IR does not contain control flow, therefore we
cannot express an acquire spin-loop that waits for a value to be written.
Instead, we can use a `#push` directive to establish that we only consider the
case where the acquire load reads from a certain release store as follows
(`$A -> $B in rf` means that the load `$B` reads from the store `$A`):

```
#thread 0
...
  $A: store.release flag
...

#thread 1
...
  $B: load.acquire flag
...

#push ($A -> $B) in rf
```

