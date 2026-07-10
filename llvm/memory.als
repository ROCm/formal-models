module memory_consistency/llvm/memory

// This module defines events that access memory and related constraints.

open memory_consistency/llvm/events

open util/relation

// Accesses are events that operate on specified memory locations. The identity
// of the memory location itself is not important. We abstract it out by
// relating all Accesses that specify the same memory location.
abstract sig Access extends Event {
  same_location : set Access
}

fact same_location_equivalence {
  equivalence[same_location, Access]
}

// Events that read from memory. Not mutually exclusive with Write.
sig Read in Access { }

// Reads in this signature read undef because of a data race.
sig DataRaceRead in Read { }

// Events that write to memory. Not mutually exclusive with Read.
sig Write in Access {
  // The successors in the modification order for Monotonic operations.
  mo : set Write,

  // All Reads that read from this Write.
  rf : set Read
}

fact access_relations {
  rf in same_location
  mo in same_location
  mo = ^mo

  // Every Read R reads from at most one Write W. If W does not exist, then R
  // reads undef because of a data race.
  all R : Read | lone rf.R and (no rf.R iff R in DataRaceRead)
}

// Next Write in the modification order. There may be more than one for cases
// where the modification order is not total, e.g., because syncscopes are
// involved.
fun mo_imm : Write -> Write {
  {a, c: Write | (a -> c) in mo and no b: Write | (a -> b) + (b -> c) in mo}
}

// Signature for Writes that don't Read.
sig SimpleWrite extends Access { }

// Signature for Reads that don't Write.
sig SimpleRead extends Access { }

// Signature for Accesses that Write and Read.
sig RMW extends Access { }

fact rmw_inclusions {
  SimpleWrite = Write - Read
  SimpleRead = Read - Write
  RMW = Read & Write
}

// Signature for initialization events. They are Writes that happen before all
// other events; there is exactly one per memory location.
sig Init extends SimpleWrite { }

// Set of Reads that read the initial value of their location.
fun InitRead : set Read {
  Init.rf
}

// Relation that orders initialization events before all other events.
// happens-before implementations will want to include this.
fun initializes_before : Init -> Event {
  Init -> (Event - Init)
}

fact init_properties {
  // We consider initialization to happen outside of the threads, so they are
  // not program ordered. The hb definition should order them separately before
  // all other events.
  no Init.po_imm and no po_imm.Init

  // Exactly one initialization per location.
  all disj I1, I2 : Init | (I1 -> I2) not in same_location
  all A : Access | one I : Init | (I -> A) in same_location
  // Note: Different formulations of this with potentially different performance
  //       are conceivable.
}

// Connects Accesses to the same location between which a Write to the same
// location is ordered by the given relation.
// Note: This should be used carefully since it can have a severe performance
// impact, depending on the context in which it is used.
fun write_between[rel: Access -> Access] : Access -> Access {
  let same_loc_rel = rel & same_location |
  (same_loc_rel :> Write).same_loc_rel
}
