module memory_consistency/llvm/openshmem_model

// Top-level OpenSHMEM API-level memory model. A finite execution is valid under
// the OpenSHMEM API-level memory model iff it corresponds to an Alloy instance
// of this module.
//
// -----------------------------------------------------------------------------
// Step 4 (Fused collectives) - DESIGN NOTE / PARTIAL
// -----------------------------------------------------------------------------
// A matched set of collective calls (one per PE in a team) is, per the spec,
// "fused" into a single operation event spanning all participating PEs. A
// literally shared single event across N threads collides with the base
// invariant `lone E.~po_imm` (each event has at most one program-order
// predecessor), because a fused op would sit in every participating thread's
// program order simultaneously.
//
// The intended representation (not fully wired into openshmem_predicates yet) is
// to keep one Operation event *per PE* and relate the matched calls with an
// equivalence relation `fused_with : Operation -> Operation`, then have the
// cross-PE ordering relations (in particular rco for barrier/quiet) quantify
// over the whole fused class rather than a single atom. Concretely, rco's
// "hb-before / hb-after a barrier" clauses would use `hb ; fused_with` and
// `fused_with ; hb` so that ordering established at any PE's copy propagates to
// all copies. This is documented as future work in
// OPENSHMEM_EXTENSION_REPORT.md; barrier is currently modeled only via its
// per-PE operation events participating in rco (single-PE reasoning).

open memory_consistency/llvm/openshmem_predicates

fact {
  openshmem_memory_model
}
