module memory_consistency/llvm/openshmem_predicates_c11

// OpenSHMEM API-level memory model over the spec's simplified C++/C11 axioms.
//
// The OpenSHMEM specification (api_mem_model.tex) defines its API-level model as
// an extension of the C++ memory model, and explicitly leaves out the SC and
// consume memory orders "for simplicity", using just: acyclic(api_hb),
// irreflexive(rf; api_hb), the coherence axiom, and RMW atomicity. This module
// transcribes exactly that axiom set (a faithful C11-flavored transcription of
// the spec).
//
// For an alternative that instead extends the repo's fuller LLVM memory model
// (monotonic / unordered / seqcst tiers), see openshmem_predicates.als.
//
// The API-level relations, api_hb, api_may_see, api_happens_before, and
// no_api_races are shared and live in openshmem_relations.als.

open memory_consistency/llvm/memory
open memory_consistency/llvm/scopes
open memory_consistency/llvm/openshmem_relations
open memory_consistency/llvm/utils

open util/relation

// Modification-order consistency over api_hb (the spec's coherence axiom). This
// is the simplified C++ coherence: mo acyclic, consistent with api_hb, and the
// coherence irreflexivity condition. Per-location total mo, the monotonic-read
// coherence rules, and seqcst are intentionally omitted (the spec leaves them
// out); the LLVM-based module reinstates them.
pred api_mo_coherence {
  acyclic[mo, Write]
  no (mo & ~api_hb)
  // coherence: irreflexive((rf^-1)? ; mo ; rf? ; api_hb)
  no (iden & ((maybe[~rf]).mo.(maybe[rf]).api_hb))
}

// The OpenSHMEM API-level memory model (C11 flavor). Scopes are not exposed at
// the API level (spec: Compatibility with a Scoped Memory Model), so all scopes
// are compatible.
pred openshmem_memory_model {
  api_happens_before
  api_mo_coherence
  all_scopes_compatible
}
