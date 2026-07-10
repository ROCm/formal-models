module memory_consistency/llvm/general_predicates

// Convenience predicates and functions for common asserts.

open memory_consistency/llvm/memory
open memory_consistency/llvm/events


// True iff all Events are atomic. This is useful to rule out data races.
pred only_atomics {
  Atomic = Event
}

// True iff all Atomics have compatible scope. This is useful to rule out data
// races.
pred only_compatible_scopes {
  compatible_scope = Atomic -> Atomic
}

// True iff the execution does not contain data races.
pred no_races {
  no DataRaceRead
}

// True iff all accesses go to the same location.
pred all_same_location {
  same_location = Access -> Access
}

// The number of threads.
fun num_threads : Int {
  // Every Event that is not a successor in the program order or an Init Event
  // starts a thread.
  #(Event - (Event.po_imm + Init))
}

