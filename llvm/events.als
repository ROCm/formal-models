module memory_consistency/llvm/events

// An execution of a program is made of Events. Events produced by a thread
// executing a program are related to each other in program order.

open util/relation

abstract sig Event {
  po_imm : lone Event,  // The immediate successor in the program order, if there is one.
}

fact po_total_order {
  // The program order is total order for each thread.
  all E : Event | lone E.~po_imm
  acyclic[po_imm, Event]
}

// Relates all Events in the same thread, which is simply the symmetric closure
// over the program order.
fun same_thread : Event -> Event { po + ~po }

// The program order is the transitive closure of po_imm.
fun po : Event -> Event { ^po_imm }

// Events can be atomic, in which case they may synchronize with other Atomics.
sig Atomic in Event {
  // If two atomics have compatible scope, their syncscopes and their position
  // in the thread topology allow them to synchronize.
  compatible_scope: set Atomic,
}

fact compatible_scope_constraints {
  // These are only general requirements on compatible_scope. Additional
  // target-specific constraints may be required.

  symmetric[compatible_scope]
  reflexive[compatible_scope, Atomic]

  // All atomics in the same thread have compatible scope.
  same_thread & (Atomic -> Atomic) in compatible_scope
}
