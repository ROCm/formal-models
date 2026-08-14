module memory_consistency/llvm/scopes

// This module implements scoped parallelism with a tree-shaped hierarchy of
// scope instances. The root of the tree is the single System scope instance.
// Events are executed in a scope instance (their execscope_instance) and
// Atomics can refer to a scope instance via their syncscope (their
// syncscope_instance).
//
// This module is self-contained: The remaining memory-model works without it if
// the compatible_scope relation is constrained in a different way.

open memory_consistency/llvm/events
open memory_consistency/llvm/memory

open util/relation

sig ScopeInstance {
  // Mapping from this scope instance to its parent scope instance (i.e., the
  // more general scope instance that directly includes it). This relation
  // encodes a tree with the System scope instance as the root: The System scope
  // instance has no parent; every other scope instance has exactly one parent;
  // following the parent relation from any scope instance eventually leads to
  // the System scope instance.
  parent : lone ScopeInstance,

  // Mapping from this scope instance to the Events that execute in it.
  // Declaring the relation this way here (instead of a potentially more
  // intuitive 'execscope_instance' relation in Event) allows us to keep
  // scope-related constructs out of the Event signature. See also the
  // execscope_instance helper defined below.
  execscope_instance_for : set Event,

  // Mapping from this scope instance to the Atomic events that have it as their
  // syncscope instance. See the analogous execscope_instance_for for the
  // rationale. See also the syncscope_instance helper defined below.
  syncscope_instance_for : set Atomic,
}

// Mapping from Events to the scope instance they execute in.
fun execscope_instance : Event -> ScopeInstance {
  ~execscope_instance_for
}

// Mapping from Atomics to their syncscope instance.
fun syncscope_instance : Atomic -> ScopeInstance {
  ~syncscope_instance_for
}

// There always is one System scope instance, which is the root of the scope
// hierarchy.
one sig System extends ScopeInstance {}

fact init_scopes {
  // Initializations are in compatible scopes with all other events.
  Init -> Atomic in compatible_scope

  // Initializations are not associated with any scope instances.
  no Init.syncscope_instance
  no Init.execscope_instance
}

fact consistent_scopes {
  // The only scope instance that has no parent is the System scope instance.
  all S : ScopeInstance | S in System iff no S.parent

  // Every other scope instance has a single parent scope instance.
  all S : ScopeInstance - System | one S.parent

  // The parent relation is acyclic, which together with the above two
  // constraints ensures that the relation encodes a tree with System as the
  // root.
  acyclic[parent, ScopeInstance]

  // Every non-Init Event executes in exactly one scope instance.
  all e : Event - Init | one e.execscope_instance

  // Every Atomic has exactly one scope instance it syncs with.
  all e : Atomic - Init | one e.syncscope_instance

  // If two events are program-ordered (i.e., in the same thread), they must
  // execute in the same scope instance.
  // We don't require an individual scope instance per thread, this simplifies
  // the model and allows the solver to omit unnecessary ScopeInstance atoms.
  po in execscope_instance.~execscope_instance

  // An Atomic's syncscope_instance must include its execscope_instance (i.e.,
  // the thread it is executing in).
  all a : Atomic - Init | a.syncscope_instance in a.execscope_instance.*parent

  // Two Atomics must have compatible scope if they have the same syncscope.
  syncscope_instance.~syncscope_instance in compatible_scope
}

// Two atomics have inclusive scope if and only if their syncscopes include each
// other's execscope.
fun inclusive_scope : Atomic -> Atomic {
  { a1, a2 : Atomic - Init |
    a1.syncscope_instance in a2.execscope_instance.*parent and
    a2.syncscope_instance in a1.execscope_instance.*parent
  }
}

// Predicate to encode that inclusive scopes are compatible scopes.
pred scope_inclusion_is_scope_compatibility {
  compatible_scope = inclusive_scope + (Init -> Atomic) + (Atomic -> Init)
}

// Predicate to encode that all scopes are compatible with each other, i.e.,
// scope compatibility does not play any role.
pred all_scopes_compatible {
  Atomic -> Atomic in compatible_scope
}

// Predicate to encode that there are only two levels of scopes (system and
// singlethread).
pred flat_scope_hierarchy {
  no ScopeInstance.parent.parent
}

// Helper functions to constrain the scope hierarchy:

// Connects each ScopeInstance to all its superscope instances (including
// itself).
fun superscope : ScopeInstance -> ScopeInstance {
  *parent
}

// Connects each ScopeInstance to all its subscope instances (including
// itself).
fun subscope : ScopeInstance -> ScopeInstance {
  ~superscope
}

// The set of scope instances that are ancestors of both s1 and s2 (including
// s1/s2 if s1 = s2).
fun common_ancestors[s1, s2 : ScopeInstance] : set ScopeInstance {
  s1.*parent & s2.*parent
}

// The least common ancestor of s1 and s2 in the scope hierarchy.
// Since the scope hierarchy is a tree, there has to be exactly one least common
// ancestor.
fun least_common_ancestor[s1, s2 : ScopeInstance] : one ScopeInstance {
  { s : ScopeInstance | s in common_ancestors[s1, s2] and all t : s.~parent | t not in common_ancestors[s1, s2] }
}
