module memory_consistency/llvm/openshmem_comid

// OpenSHMEM API-level memory model: OPTIONAL communication-identifier (com_id)
// extension.
//
// This module is additive: it does not touch the base OpenSHMEM model
// (openshmem_relations / openshmem_predicates*). Tests that want com_id semantics
// open THIS module and use `openshmem_comid_memory_model` / `no_api_races_comid`;
// everything else keeps using the base model unchanged.
//
// Idea (see the request that motivated it):
//   * Every memory access and OpenSHMEM operation carries a com_id. The com_id of
//     an operation matches that of its observable accesses (here: observable
//     accesses INHERIT their operation's com_id).
//   * com_ids form a hierarchy. A distinguished GlobalComId is the parent of (and
//     "greater than") every other com_id; if an event is untagged, its com_id is
//     GlobalComId.
//   * Each API-level relation is considered "per com_id". A relation edge is
//     established, at a given relation-com_id c, only if
//       (1) the com_id of the *triggering operation(s)* is >= c, and
//       (2) the com_id of any *non-observable access* endpoint is <= c.
//     Observable-access endpoints are NOT gated by (2): their com_id equals that
//     of their issuing operation, which is already covered by (1). (Gating them
//     again by (2) would pin c to the op's com_id and defeat the hierarchy; see
//     the notes below.) Consequently a relation whose endpoints are all
//     observable -- notably asw -- fires whenever its triggering ops' com_ids are
//     COMPARABLE (same, or ancestor/descendant), failing only for incomparable
//     (sibling) com_ids.
//   * api_hb is the UNION over c of the transitive closures of
//       (the c-gated API relations) + sw + ppo.
//     Taking the closure per-c and then unioning (rather than closing one big
//     union) means an api_hb path must thread its API-relation edges through a
//     single common com_id c (sw/ppo are shared by every c).
//   * ppo (preserved program order) relaxes po to only the pairs a sane
//     architecture keeps ordered: same-address accesses, accesses before a
//     store-release (and the release), a load-acquire (and accesses after it),
//     and accesses on either side of a memory fence.

open memory_consistency/llvm/events
open memory_consistency/llvm/memory
open memory_consistency/llvm/memory_ordering
open memory_consistency/llvm/llvm_predicates
open memory_consistency/llvm/scopes
open memory_consistency/llvm/openshmem_events
open memory_consistency/llvm/openshmem_relations
open memory_consistency/llvm/utils

open util/relation

// =============================================================================
// com_id hierarchy
// =============================================================================

sig ComId {
  // Parent in the hierarchy (the parent is "greater than" this com_id).
  com_parent : lone ComId,
  // Events explicitly tagged with this com_id. Untagged events default to
  // GlobalComId (see `comid`). Observable accesses are never tagged directly;
  // they inherit their operation's com_id.
  tagged : set Event,
}

one sig GlobalComId extends ComId {}

fact comid_hierarchy {
  // Global is the root: it has no parent and every com_id reaches it upward.
  no GlobalComId.com_parent
  all c : ComId - GlobalComId | one c.com_parent
  all c : ComId | c not in c.^com_parent          // the parent relation is acyclic
  all c : ComId | GlobalComId in c.*com_parent     // rooted at GlobalComId

  // An event carries at most one explicit tag, and observable accesses are not
  // tagged directly (they inherit from their issuing operation).
  all e : Event | lone tagged.e
  no (tagged.univ & observable_accesses)
}

// c1 >= c2  iff  c1 is an ancestor-or-self of c2 in the hierarchy.
fun com_geq : ComId -> ComId { *(~com_parent) }

// The com-id-bearing "source" of an event: its issuing operation if it is an
// observable access, otherwise the event itself.
fun comid_src[e: Event] : one Event {
  { s : Event |
      (e in observable_accesses and s = issued_by[e]) or
      (e not in observable_accesses and s = e) }
}

// The com_id of an event: the explicit tag of its source, or GlobalComId.
fun comid[e: Event] : one ComId {
  let s = comid_src[e] |
    { c : ComId | c = tagged.s or (no tagged.s and c = GlobalComId) }
}

// Condition (2) of the com_id gate: an endpoint e is admissible at relation-
// com_id c iff it is not a NON-observable access, or its com_id is <= c.
// Observable-access endpoints (and non-access endpoints such as operations) are
// exempt -- they are covered by condition (1) via their issuing operation.
pred endpoint_leq[e: Event, c: ComId] {
  e in (Access - observable_accesses) implies (c -> comid[e]) in com_geq
}

// =============================================================================
// Preserved program order (ppo)
// =============================================================================
//
// ppo keeps only the po pairs a sensible architecture will not reorder. Note
// observable accesses are program-order-exempt (no po edges), so ppo never
// orders them; all ordering of observable accesses comes from the API relations.
fun ppo : Event -> Event {
  // (a) accesses to the same address, in program order
  (po & same_location)
  // (b) accesses before a store-release, and the store-release itself
  + (Access <: po :> (Write & Release))
  // (c) a load-acquire, and accesses after it
  + ((Read & Acquire) <: po :> Access)
  // (d) accesses on either side of a memory fence (base Fence or shmem FenceOp)
  + (Access <: po :> (Fence + FenceOp))
  + ((Fence + FenceOp) <: po :> Access)
}

// =============================================================================
// com_id-gated API relations
// =============================================================================
//
// Each `*_at[c]` is the set of that relation's edges established at relation-
// com_id c: the triggering operation(s) must be >= c and both endpoints <= c.
// The geometric conditions are exactly those of the base relations
// (openshmem_relations.als); only the com_id gate is added.

// ilv: triggering op = the operation performing the local observable access B.
fun ilv_at[c: ComId] : Access -> Access {
  { A : Access, B : Access |
    B in observable_accesses and
    (let op = issued_by[B] |
       (A -> op) in pl_hb and
       B.target_pe = op.home_pe and
       A.target_pe = op.home_pe and
       (comid[op] -> c) in com_geq and
       endpoint_leq[A, c] and endpoint_leq[B, c]) }
}

// lco: triggering op = the blocking operation performing the local access A.
fun lco_at[c: ComId] : Access -> Event {
  { A : Access, B : Event |
    A in observable_accesses and
    (let op = issued_by[A] |
       op in blocking_ops and
       A.target_pe = op.home_pe and
       ( (op -> B) in pl_hb or
         (B in observable_accesses and (op -> issued_by[B]) in pl_hb) ) and
       (comid[op] -> c) in com_geq and
       endpoint_leq[A, c] and endpoint_leq[B, c]) }
}

// rdo: triggering op = the fence.
fun rdo_at[c: ComId] : Access -> Access {
  { A : Access, B : Access |
    B in observable_accesses and
    (some Fop : FenceOp |
       ( ( (A -> Fop) in pl_hb and (Fop -> issued_by[B]) in pl_hb and Fop not in NoStore )
         or
         ( A in observable_accesses and issued_by[A] in fence_ordered_ops and
           (issued_by[A] -> Fop) in pl_hb and (Fop -> issued_by[B]) in pl_hb and
           A.target_pe = B.target_pe ) )
       and (comid[Fop] -> c) in com_geq
       and endpoint_leq[A, c] and endpoint_leq[B, c]) }
}

// rco: triggering op = the quiet/barrier.
fun rco_at[c: ComId] : Access -> Access {
  { A : Access, B : Access |
    (some QB : (QuietOp + BarrierOp) |
       ( ( A not in observable_accesses and B not in observable_accesses and
           (A -> QB) in pl_hb and (QB -> B) in pl_hb and QB not in NoStore )
         or
         ( A not in observable_accesses and B in observable_accesses and
           (A -> QB) in pl_hb and (QB -> issued_by[B]) in pl_hb and QB not in NoStore )
         or
         ( A in observable_accesses and (issued_by[A] -> QB) in pl_hb and
           ( (B not in observable_accesses and (QB -> B) in pl_hb) or
             (B in observable_accesses and (QB -> issued_by[B]) in pl_hb) ) )
         or
         ( A in observable_accesses and issued_by[A] in qb_ordered_ops and
           (issued_by[A] -> QB) in pl_hb and
           B in observable_accesses and (QB -> issued_by[B]) in pl_hb ) )
       and (comid[QB] -> c) in com_geq
       and endpoint_leq[A, c] and endpoint_leq[B, c]) }
}

// asw: triggering ops = the synchronizing write op AND read op (both >= c).
fun asw_at[c: ComId] : Write -> Read {
  { W : Write, R : Read |
    W in observable_accesses and R in observable_accesses and
    (W -> R) in rf and
    issued_by[W] in asw_ops and issued_by[R] in asw_ops and
    (comid[issued_by[W]] -> c) in com_geq and
    (comid[issued_by[R]] -> c) in com_geq and
    endpoint_leq[W, c] and endpoint_leq[R, c] }
}

// =============================================================================
// api_hb (com_id flavored) and the shared happens-before / data-race axiom
// =============================================================================

// Shared, com_id-independent backbone: preserved program order, PL
// synchronizes-with, intra-operation dependency order, and initialization order.
fun comid_backbone : Event -> Event {
  ppo + llvm_sw + Operation.op_sb + initializes_before
}

// All c-gated API-relation edges at a given com_id c.
fun rels_at[c: ComId] : Event -> Event {
  ilv_at[c] + lco_at[c] + rdo_at[c] + rco_at[c] + asw_at[c]
}

// api_hb: union over com_ids of the per-com_id transitive closures.
fun api_hb_comid : Event -> Event {
  { x : Event, y : Event |
      some c : ComId | (x -> y) in ^(rels_at[c] + comid_backbone) }
}

// Writes a Read may read from under api_hb_comid without violating causality.
fun api_may_see_comid : Write -> Read {
  (Write <: same_location :> Read) - (write_between[api_hb_comid] + ~api_hb_comid + iden)
}

pred api_happens_before_comid {
  acyclic[api_hb_comid, Event]

  rf in api_may_see_comid

  all R : Read | R in DataRaceRead iff (
      let involved = R + api_may_see_comid.R |
        (involved not in Atomic or (involved -> involved) not in compatible_scope)
          and (#api_may_see_comid.R >= 2)
    )
}

pred no_api_races_comid { no DataRaceRead }

// Modification-order consistency over api_hb_comid (the spec's simplified C11
// coherence axiom, retargeted to the com_id happens-before).
pred api_mo_coherence_comid {
  acyclic[mo, Write]
  no (mo & ~api_hb_comid)
  no (iden & ((maybe[~rf]).mo.(maybe[rf]).api_hb_comid))
}

// The OpenSHMEM API-level memory model with com_id happens-before (C11 flavor).
pred openshmem_comid_memory_model {
  api_happens_before_comid
  api_mo_coherence_comid
  all_scopes_compatible
}
