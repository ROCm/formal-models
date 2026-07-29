# OpenSHMEM API-Level Litmus Tests — Status Report

This report summarizes every OpenSHMEM litmus test currently in the
`formal-models` repo under `llvm/test/openshmem/`. Each test hand-encodes a
concrete execution in Alloy and asserts, via `run ... expect 0|1`, that the
intended outcome is satisfiable (SAT) and that forbidden alternatives are
unsatisfiable (UNSAT). All tests open `openshmem_predicates_c11` (the OpenSHMEM
spec's simplified C++/C11 axioms) unless noted otherwise.

There are two groups:

- **Part A — Canonical family suite** (`canonical/`): the classic weak-memory
  litmus families (MP, SB, LB, IRIW, WRC, RWC, CoWW, ISA2), each with a race-free
  all-API version, relaxation variants, and a race-inducing version.
- **Part B — Targeted relation tests** (`api_relations/`): each isolates one
  API-level ordering relation (ilv/lco/rdo/rco/asw), with relaxation/race
  variants where they are meaningful.
- **Part C — com_id extension** (`canonical/mp/comid/`): MP variants exercising
  the optional communication-identifier layer, where matching (or comparable)
  com_ids recover the original behavior and incomparable com_ids induce a race or
  non-SC behavior.

All 25 Part A files, all 19 Part B files, and all 5 Part C files pass their
checks.

---

## Model background needed to read the tests

An OpenSHMEM operation (put, get, atomic, fence, quiet, wait) is an `Operation`
event that *issues* one or more observable memory accesses. Observable accesses
take part in read-from (rf) and modification order (mo) like ordinary accesses,
but are **program-order-exempt**: there is no po edge between an operation's
observable accesses and the issuing thread. Ordering among them comes only from
the API-level relations:

- **ilv** (implicit local visibility): a *local* observable access sees prior
  hb-ordered accesses of the initiating PE.
- **lco** (local completion order): a *blocking* op's *local* observable
  accesses complete before subsequent hb-ordered events of the caller.
  **lco is local-only** — it never orders a subsequent *remote* access.
- **rdo** (remote delivery order, i.e. `shmem_fence`): case (i) a prior memory
  access is ordered before a later op's observable accesses; case (ii) two
  fence-separated observable accesses **to the same target PE** are ordered.
- **rco** (remote completion order, i.e. `shmem_quiet`/barrier): *full*
  connectivity across the operation, including across *different* target PEs —
  something a fence cannot provide.
- **asw** (API synchronizes-with): an observable write of an atomic / signaling /
  p2p-sync / lock op synchronizes with the observable read that reads from it.

`api_hb` is the transitive closure of program order, intra-op dependencies, and
all five relations above. A **data race** exists when a read could read from two
or more candidate writes and at least one involved access is non-atomic.

Key consequence used throughout: a **remote atomic** access (target PE != home
PE) is atomic (so it cannot race) but earns **no ilv, no lco, no rdo** — it is
the OpenSHMEM analog of a *relaxed atomic*. Ordinary (non-atomic) accesses can
race; atomic accesses synchronize via asw when one reads from the other.

Convention: `a@PEk` is object `a`'s copy on PE k.

---

# Part A — Canonical family suite

Each family is built around an **api-only reference execution**: every access is
an OpenSHMEM API call (using *atomic* remote accesses wherever an ordering
guarantee is needed), fully synchronized, race-free, and — for the families that
admit it — enforcing the sequentially-consistent (SC-for-DRF) outcome by
forbidding the weak result. Each variant modifies that reference in one of three
ways:

- **partial-normal** — replace some API calls with ordinary (non-atomic) loads/
  stores, keeping any racing pair *homogeneous* (both API or both normal). A
  partial-normal variant must retain the **same** behavior as the api-only
  reference: race-free and SC.
- **relaxation** (remote-atomic, or an added/removed fence) — deliberately drop
  one ordering guarantee. The result is either *non-SC but still race-free*
  (accesses stay atomic, so no race, but the weak outcome becomes allowed), or,
  where the dropped ordering was load-bearing for delivery, a *data race*.
- **race (all-normal)** — demote every access to ordinary put/get, removing both
  atomicity and synchronization, to exhibit the data race.

For each variant below the **SC verdict** is one of: *SC* (race-free and the weak
outcome is forbidden — verified by the named UNSAT check), *non-SC* (race-free but
the weak outcome is allowed), or *racy* (a data race exists). Two families — SB
and IRIW — have **no** SC api-only reference at all: no OpenSHMEM primitive can
forbid their weak outcome (see their notes), so their reference is the race-free
*non-SC* execution.

## A1. MP — Message Passing

Does synchronization carry prior ordinary writes to the consumer?

```
P0: x = 1 ; release(flag = 1)
P1: r0 = acquire(flag) ; r1 = x
Forbidden weak outcome: r0 == 1 && r1 == 0
```

**mp-all-api** — api-only reference. **SC.** Race-free; the weak outcome is
forbidden (`cannot_read_stale_x` UNSAT, `no_data_race` UNSAT).
```
PE0: shmem_put(x, xsrc, pe1)        # LD xsrc@PE0 ; ST x@PE1
     shmem_fence()
     shmem_atomic_set(flag, 1, pe1) # ST flag@PE1 (atomic)
PE1: shmem_wait_until(flag == 1)    # LD flag@PE1 (atomic, local)
     shmem_get(r, x, pe1)           # LD x@PE1 (local self-get)
```
The chain `put.ST(x) --rdo--> set.ST(flag) --asw--> wait.LD(flag) --lco-->
get.LD(x)` forces the get to observe the put once the flag is seen.

**mp-partial-normal-data** — *partial-normal.* Replaces the DATA accesses with
ordinary ones (a direct remote store via `shmem_ptr` on the producer, a plain
local load on the consumer); the flag synchronization stays API. The racing data
pair is homogeneous (both normal). **SC retained** — identical verdicts to the
reference (`cannot_read_stale_x` UNSAT, `no_data_race` UNSAT).
```
PE0: *ptr_to_PE1_x = 1              # normal ST x@PE1 (remote)   <-- was shmem_put
     shmem_fence()
     shmem_atomic_set(flag, 1, pe1) # ST flag@PE1 (atomic)
PE1: shmem_wait_until(flag == 1)    # LD flag@PE1 (atomic, local)
     r1 = x                         # normal LD x@PE1            <-- was shmem_get
```
Why SC survives the substitution: the fence still gives `st_x --rdo--> set.ST(flag)`
(the normal store is a memory access before the fence, rdo case i), and
`set.ST(flag) --asw--> wait.LD(flag) --lco--> r1=x` orders the consumer's plain
load after the wait — so the ordinary load still observes the delivered x.

**mp-race-nofence** — *relaxation:* drop the fence. **racy.** Without `rdo` the
put's store of x is unordered relative to the flag, so the get's read of x races
with the put (`race_on_x` SAT).
```
PE0: shmem_put(x, xsrc, pe1)
     shmem_atomic_set(flag, 1, pe1) # <-- fence removed
PE1: shmem_wait_until(flag == 1)
     shmem_get(r, x, pe1)
```

**mp-race-remote-sync** — *relaxation:* move the flag to a third PE and observe it
with a *remote* atomic_fetch instead of a local wait. **racy.** `lco` is
local-only, so the remote fetch does not order the subsequent local get; the get's
read of x races (`race_on_x` SAT). Restoring the order would need a quiet (rco),
not a fetch.
```
PE0: shmem_put(x, xsrc, pe1)
     shmem_fence()
     shmem_atomic_set(flag, 1, pe2)      # flag now on PE2
PE1: r0 = shmem_atomic_fetch(flag, pe2)  # LD flag@PE2 (atomic, REMOTE)  <-- was local wait
     shmem_get(r, x, pe1)
```

## A2. SB — Store Buffering / Dekker

Can a store then load appear reordered?

```
P0: x = 1 ; r0 = y
P1: y = 1 ; r1 = x
Weak outcome: r0 == 0 && r1 == 0
```

x and y are both hosted on a third PE (PE2), so every shared access is remote.
**SB has no api-only SC reference** (see the finding below); the reference is the
race-free *non-SC* remote-atomic execution.

**sb-all-api-relaxed** — api-only reference, remote atomics, no fence. **non-SC.**
Race-free (atomic), weak outcome allowed (`weak_outcome_allowed` SAT,
`no_data_race` UNSAT). Remote atomics earn no ilv/lco/rdo, so nothing orders each
PE's store before its load.
```
PE0: shmem_atomic_set(x, 1, pe2)                 ; r0 = shmem_atomic_fetch(y, pe2)
PE1: shmem_atomic_set(y, 1, pe2)                 ; r1 = shmem_atomic_fetch(x, pe2)
```

**sb-all-api-fence** — *relaxation attempt:* add a fence between each PE's set and
fetch. **still non-SC.** Race-free, but the weak outcome remains allowed
(`weak_outcome_still_allowed` SAT).
```
PE0: shmem_atomic_set(x, 1, pe2) ; shmem_fence() ; r0 = shmem_atomic_fetch(y, pe2)
PE1: shmem_atomic_set(y, 1, pe2) ; shmem_fence() ; r1 = shmem_atomic_fetch(x, pe2)
```
**Finding — a fence does NOT restore SC for SB.** Forbidding SB needs to close a
*from-read* cycle
`st_x --order--> ld_y --fr--> st_y --order--> ld_x --fr--> st_x`,
i.e. a **store->load (sequentially consistent) fence**. `shmem_fence` only adds
`api_hb` edges (rdo), and the model checks `acyclic(api_hb)`; the from-read edges
are not in `api_hb`, and the spec's simplified axioms omit SC. So no OpenSHMEM
primitive (fence, quiet, or barrier) restores SC for SB.

**sb-race-normal** — *race:* demote both remote atomics to normal put/get.
**racy.** The cross accesses to x and y are non-atomic and unsynchronized
(`race_reachable` SAT).
```
PE0: shmem_put(x, ..., pe2)                      ; r0 = shmem_get(y, pe2)
PE1: shmem_put(y, ..., pe2)                      ; r1 = shmem_get(x, pe2)
```

## A3. LB — Load Buffering

Can a load then store appear reordered?

```
P0: r0 = x ; y = 1
P1: r1 = y ; x = 1
Weak outcome: r0 == 1 && r1 == 1
```

x and y hosted on PE2; all shared accesses remote.

**lb-all-api-relaxed** — api-only, remote atomics, no fence. **non-SC.** Race-free;
weak outcome allowed (`weak_outcome_allowed` SAT).
```
PE0: r0 = shmem_atomic_fetch(x, pe2)                 ; shmem_atomic_set(y, 1, pe2)
PE1: r1 = shmem_atomic_fetch(y, pe2)                 ; shmem_atomic_set(x, 1, pe2)
```

**lb-all-api-sc** — api-only SC reference: add a fence between each PE's fetch and
set. **SC.** Race-free; weak outcome forbidden (`weak_outcome_forbidden` UNSAT).
```
PE0: r0 = shmem_atomic_fetch(x, pe2) ; shmem_fence() ; shmem_atomic_set(y, 1, pe2)
PE1: r1 = shmem_atomic_fetch(y, pe2) ; shmem_fence() ; shmem_atomic_set(x, 1, pe2)
```
**The SB/LB asymmetry:** unlike SB, LB *is* restored by a plain fence. The fence
gives `ld --rdo--> st` on each PE, and the weak outcome's cross reads give
`st --asw--> ld`; together they close a cycle **entirely within api_hb**:
`ld_x --rdo--> st_y --asw--> ld_y --rdo--> st_x --asw--> ld_x`, which
`acyclic(api_hb)` forbids. LB needs only delivery (release/acquire-style)
ordering, which rdo provides; SB needs a full SC fence, which OpenSHMEM lacks.

**lb-race-normal** — *race:* demote to normal get/put. **racy** (`race_reachable`
SAT).
```
PE0: r0 = shmem_get(x, pe2)                          ; shmem_put(y, ..., pe2)
PE1: r1 = shmem_get(y, pe2)                          ; shmem_put(x, ..., pe2)
```

## A4. IRIW — Independent Reads of Independent Writes

Do two observers agree on the order of two independent writes?

```
P0: x = 1        P1: y = 1
P2: r0 = x ; r1 = y      P3: r2 = y ; r3 = x
Weak outcome: r0==1 && r1==0 && r2==1 && r3==0
```

x and y hosted on PE4; all four PEs access remotely. **Like SB, IRIW has no
api-only SC reference** (see the note); the reference is the race-free non-SC
remote-atomic execution.

**iriw-all-api-relaxed** — api-only reference, remote atomics, no fences.
**non-SC.** Race-free; weak outcome allowed (`weak_outcome_allowed` SAT). Remote
atomics are not multi-copy atomic, so observers need not agree on a global write
order.
```
PE0: shmem_atomic_set(x, 1, pe4)
PE1: shmem_atomic_set(y, 1, pe4)
PE2: r0 = shmem_atomic_fetch(x, pe4)                 ; r1 = shmem_atomic_fetch(y, pe4)
PE3: r2 = shmem_atomic_fetch(y, pe4)                 ; r3 = shmem_atomic_fetch(x, pe4)
```

**iriw-all-api-fence** — *relaxation attempt:* fence between each observer's two
reads. **still non-SC** (`weak_outcome_still_allowed` SAT). The fence orders each
observer's *own* two reads (rdo) but cannot force the two observers to agree.
```
PE2: shmem_atomic_fetch(x, pe4) ; shmem_fence() ; shmem_atomic_fetch(y, pe4)
PE3: shmem_atomic_fetch(y, pe4) ; shmem_fence() ; shmem_atomic_fetch(x, pe4)
```
**Note — a fence is insufficient for IRIW** (as for SB): forbidding it requires
multi-copy atomicity / a global SC order, i.e. a from-read cycle not present in
`api_hb`, which no OpenSHMEM primitive supplies.

**iriw-race-normal** — *race:* demote to normal put/get. **racy**
(`race_reachable` SAT).

## A5. WRC — Write-to-Read Causality

Does causality propagate through a read then a (dependent) write?

```
P0: x = 1
P1: r0 = x ; if (r0==1) y = 1
P2: r1 = y ; r2 = x
Weak outcome: r0==1 && r1==1 && r2==0
```

x, y hosted on PE3.

**wrc-all-api** — api-only SC reference: remote atomics with a fence on P1
(read x -> write y) and on P2 (read y -> read x). **SC.** Race-free; weak outcome
forbidden (`weak_outcome_forbidden` UNSAT).
```
PE0: shmem_atomic_set(x, 1, pe3)
PE1: r0 = shmem_atomic_fetch(x, pe3) ; shmem_fence() ; shmem_atomic_set(y, 1, pe3)
PE2: r1 = shmem_atomic_fetch(y, pe3) ; shmem_fence() ; r2 = shmem_atomic_fetch(x, pe3)
```
The causal chain `st_x --asw--> ld_x1 --rdo--> st_y --asw--> ld_y2 --rdo--> ld_x2`
lies entirely within `api_hb`, so once P2 observes y it must observe st_x.

**wrc-relaxed** — *relaxation:* remove both fences. **non-SC.** Race-free (atomic),
but the weak outcome becomes allowed (`weak_outcome_allowed` SAT): the two rdo
links break, so P2 can observe y without x.
```
PE0: shmem_atomic_set(x, 1, pe3)
PE1: r0 = shmem_atomic_fetch(x, pe3) ; shmem_atomic_set(y, 1, pe3)      # fences removed
PE2: r1 = shmem_atomic_fetch(y, pe3) ; r2 = shmem_atomic_fetch(x, pe3)
```

**wrc-race-normal** — *race:* demote to normal put/get. **racy**
(`race_reachable` SAT).

## A6. RWC — Read-to-Write Causality

Like WRC, but P1's write of y is plain program order (no value dependency).

```
P0: x = 1
P1: r0 = x ; y = 1
P2: r1 = y ; r2 = x
Weak outcome: r0==1 && r1==1 && r2==0
```

x, y hosted on PE3.

**rwc-all-api** — api-only SC reference: fence on P1 and on P2. **SC.** Race-free;
weak outcome forbidden (`weak_outcome_forbidden` UNSAT).
```
PE0: shmem_atomic_set(x, 1, pe3)
PE1: r0 = shmem_atomic_fetch(x, pe3) ; shmem_fence() ; shmem_atomic_set(y, 1, pe3)
PE2: r1 = shmem_atomic_fetch(y, pe3) ; shmem_fence() ; r2 = shmem_atomic_fetch(x, pe3)
```
In this API model **RWC coincides with WRC**: observable accesses are program-
order-exempt and OpenSHMEM tracks no dependency ordering, so P1's read->write
carries no order without a fence — the value dependency present in WRC buys
nothing extra here.

**rwc-relaxed** — *relaxation:* remove both fences. **non-SC.** Race-free; weak
outcome allowed (`weak_outcome_allowed` SAT). The instructive case: even though P1
reads x (seeing 1) and then writes y in program order, P2 may observe y without x.
```
PE0: shmem_atomic_set(x, 1, pe3)
PE1: r0 = shmem_atomic_fetch(x, pe3) ; shmem_atomic_set(y, 1, pe3)      # fences removed
PE2: r1 = shmem_atomic_fetch(y, pe3) ; r2 = shmem_atomic_fetch(x, pe3)
```

**rwc-race-normal** — *race:* demote to normal put/get. **racy**
(`race_reachable` SAT).

## A7. CoWW / CoRR — Single-Location Coherence

Can one observer read two writes to a single location in backward order?

```
P0: x = 1 ; x = 2          (coherence order pinned: 1 then 2)
P1: r0 = x ; r1 = x
Backward outcome: r0 == 2 && r1 == 1
```

One PE issues both writes with a fence between them to pin the coherence order
(x=1 before x=2); x hosted on PE2. Here "SC" means single-location coherence
(CoRR): a later read must not observe an earlier write than an earlier read did.

**coww-all-api** — api-only reference: writes pinned (fence between the two
atomic_sets) and the observer's two reads fence-ordered. **SC (coherent).**
Race-free; backward outcome forbidden (`backward_outcome_forbidden` UNSAT).
```
PE0: shmem_atomic_set(x, 1, pe2) ; shmem_fence() ; shmem_atomic_set(x, 2, pe2)
PE1: r0 = shmem_atomic_fetch(x, pe2) ; shmem_fence() ; r1 = shmem_atomic_fetch(x, pe2)
```
With the read fence `ld_a --rdo--> ld_b`; because the accesses are atomic (AMO),
read-from yields asw, so if ld_a reads st2 then
`st1 --rdo--> st2 --asw--> ld_a --rdo--> ld_b` makes st2 hb-between st1 and ld_b,
and `api_may_see` excludes st1 as a source for ld_b. This holds even under the
simplified C11 axioms (no per-location total mo needed) — the AMO asw edges carry
the coherence order.

**coww-relaxed** — *relaxation:* drop the fence between the observer's two reads
(writes still pinned). **non-coherent.** Race-free (atomic), but the backward
outcome becomes allowed (`backward_outcome` SAT): with the reads unordered, CoRR
cannot bite.
```
PE0: shmem_atomic_set(x, 1, pe2) ; shmem_fence() ; shmem_atomic_set(x, 2, pe2)
PE1: r0 = shmem_atomic_fetch(x, pe2) ; r1 = shmem_atomic_fetch(x, pe2)  # read fence removed
```

**coww-race-normal** — *race:* demote to normal put/get. **racy**
(`race_reachable` SAT).

## A8. ISA2 — Transitive Synchronization

Does synchronization compose across a chain of producer-consumer hops?

```
P0: x = 1 ; release(a = 1)
P1: r0 = acquire(a) ; release(b = 1)
P2: r1 = acquire(b) ; r2 = x
Weak outcome: r0==1 && r1==1 && r2==0
```

x, a, b all hosted on PE3.

**isa2-all-api** — api-only SC reference: a fence on each PE (incoming access ->
outgoing release; and P2's b-read -> x-read). **SC.** Race-free; weak outcome
forbidden (`weak_outcome_forbidden` UNSAT).
```
PE0: shmem_atomic_set(x, 1, pe3)     ; shmem_fence() ; shmem_atomic_set(a, 1, pe3)
PE1: r0 = shmem_atomic_fetch(a, pe3) ; shmem_fence() ; shmem_atomic_set(b, 1, pe3)
PE2: r1 = shmem_atomic_fetch(b, pe3) ; shmem_fence() ; r2 = shmem_atomic_fetch(x, pe3)
```
WRC extended by one synchronization hop: the transitive chain
`st_x --rdo--> set_a --asw--> ld_a --rdo--> set_b --asw--> ld_b --rdo--> ld_x2`
lies entirely within `api_hb`, so once P2 completes the a->b chain it must observe
st_x. asw + rdo compose transitively, so synchronization chains propagate prior
writes.

**isa2-relaxed** — *relaxation:* remove all three fences. **non-SC.** Race-free;
weak outcome allowed (`weak_outcome_allowed` SAT): the rdo links break, so P2
completes the a->b sync without observing x.
```
PE0: shmem_atomic_set(x, 1, pe3)     ; shmem_atomic_set(a, 1, pe3)      # fences removed
PE1: r0 = shmem_atomic_fetch(a, pe3) ; shmem_atomic_set(b, 1, pe3)
PE2: r1 = shmem_atomic_fetch(b, pe3) ; r2 = shmem_atomic_fetch(x, pe3)
```

**isa2-race-normal** — *race:* demote to normal put/get (also removes the asw
synchronizations). **racy** (`race_reachable` SAT).

---

# Part B — Targeted relation tests (`api_relations/`)

Each isolates one API-level ordering relation, organized under
`api_relations/<relation>/`. Where relaxing the ordering yields more non-SC
behavior or a data race, a companion variant sits alongside the race-free base
test (mirroring the canonical suite). 19 files total, all pass.

## ilv — implicit local visibility (`api_relations/ilv/`)
- **ilv-put-reads-local-store** — `source = 1 ; put(dest, source, pe1)`: the put
  must read the local store (`store --ilv--> put.LD(source)`). No race.
- **ilv-get-overwrites-local-store** — `dest = 1 ; get(dest, source, pe1) ; x =
  dest`: the get's store overwrites, so the later read sees the get's value. No
  race.
- **ilv-local-load-before-get-store** — `x = dest ; get(dest, source, pe1)`: the
  local load is ordered before the get's store and cannot read it. No race.

ilv is an unconditional guarantee for local accesses, so it has no meaningful
race relaxation without changing the test's meaning (there is no ordering to
remove).

## lco — local completion order (`api_relations/lco/`)
- **lco-put-store-after-src** — `put(dest, source, pe1) ; source = 1`: the
  blocking put's source-load completes before the later store. No race.
- **lco-get-load-after-dst** — `get(dest, source, pe1) ; x = dest`: the get's
  local store completes before the later load, which must read it. No race.
- **lco-put-nbi-store-race** *(relaxation)* — the put made **non-blocking**: lco
  applies only to blocking ops, so the source-load is no longer ordered before
  the later store to the same buffer -> **data race**. (Formalizes "quiet after a
  non-blocking put before reusing the source buffer".)
- **lco-get-nbi-load-race** *(relaxation)* — the get made **non-blocking**: the
  local load races with the get's destination-store -> **data race**.

## rdo — remote delivery order / fence (`api_relations/rdo/`)
- **remote-store-fence-flag** — MP where the payload is delivered by a *direct
  remote store* (normal access, remote target), exercising rdo case (i). No race.
- **rdo-put-fence-put** — two puts to the same remote address across a fence: rdo
  case (ii) orders them; the second wins. No race.
- **rdo-put-put-race** *(relaxation)* — the same two puts with **no fence**:
  unordered conflicting writes -> **write-write data race**.
- **rdo-put-fence-get-load** — put; fence; get reading it back; local load: an
  ordered copy chain `a -> PE1:b -> PE0:c -> read`. No race.
- **rdo-put-get-load-race** *(relaxation)* — same copy chain with **no fence**:
  the get's read of b@PE1 **races** with the put's store.
- **rdo-fence-orders-store-local-sync** — a fence orders a prior *normal* store
  (rdo case i) before an atomic_set, delivered through a *local* wait. No race.
- **rdo-fence-orders-store-remote-sync** *(FINDING: races)* — same, but the
  consumer synchronizes through a *remote* atomic_fetch. **Data race**: lco is
  local-only, so the remote fetch does not order the subsequent remote get.
- **rdo-nofence-store-local-sync-race** *(relaxation)* — the local-sync version
  with the fence removed: without rdo the prior normal store is unordered ->
  **data race**.

## rco — remote completion order / quiet (`api_relations/rco/`)
- **rco-quiet-orders-put-cross-pe** — a quiet establishes cross-PE completion
  ordering that a fence cannot: the put's store (PE1) and the atomic_set's store
  (PE2) target *different* PEs, so rdo case (ii) cannot order them; rco (case 4,
  full connectivity) can. No race; the get is guaranteed to load the put's value.
- **rco-fence-insufficient-cross-pe-race** *(relaxation)* — the quiet replaced by
  a **fence**: rdo case (ii) cannot order accesses to different target PEs, so the
  consumer's get races with the put -> **data race**. The negative companion that
  shows why the quiet (rco) was needed.

## asw — API synchronizes-with (`api_relations/asw/`)
- **put-fence-flag** — canonical MP: put delivers data, a fenced atomic_set raises
  the flag, a waiter consumes it. The atomic flag supplies asw
  (`put.ST --rdo--> set.ST --asw--> wait.LD --lco--> load`). No race.
- **mp-nonsync-flag-race** *(relaxation)* — the flag raised/consumed with
  **non-atomic** (non-synchronizing) accesses: no asw is formed, so nothing orders
  the delivery before the consumer's read. **Data race** — there is no race-free
  execution at all.

---

# Part C — com_id extension (optional)

An optional communication-identifier (com_id) layer lives in
`llvm/openshmem_comid.als`. It is additive: the base model and every Part A/B test
are unchanged. Tests opt in by opening `openshmem_comid` and using
`openshmem_comid_memory_model` / `no_api_races_comid`.

## The extension

- Every access and operation carries a com_id; observable accesses inherit their
  operation's com_id; untagged events default to the global com_id — the top of a
  parent/child hierarchy (greater than all other com_ids).
- Each API relation is gated per com_id c: an edge is established only if
  (1) its triggering operation(s) have com_id >= c, and (2) any *non-observable
  access* endpoint has com_id <= c. Observable-access endpoints are exempt from
  (2) — they are already covered by (1) through their issuing operation. So a
  relation whose endpoints are all observable (notably **asw**) fires whenever its
  triggering ops' com_ids are **comparable** (equal, or ancestor/descendant) and
  fails only for **incomparable (sibling)** com_ids.
- `api_hb` is the UNION over c of the transitive closures of the c-gated relations
  together with `sw` and preserved program order (`ppo`). Closing per-com_id and
  then unioning means an api_hb path threads its API-relation edges through a
  single common com_id; only sw and ppo bridge across com_ids.
- `ppo` relaxes program order to the pairs a sane architecture keeps: same-address
  accesses, accesses before a store-release (and the release), a load-acquire (and
  accesses after it), and accesses on either side of a fence.

## MP variants (`canonical/mp/comid/`, all validated)

| File | com_ids | Data race? | Outcome |
|---|---|---|---|
| mp-comid-match | one shared C1 | no | **SC** — recovers plain MP (stale x forbidden) |
| mp-comid-parent-child | producer child, consumer parent (comparable) | no | **SC** — comparable com_ids still synchronize |
| mp-comid-atomic-match | one shared C1, atomic data | no | **SC** — stale x forbidden |
| mp-comid-mismatch-race | producer/consumer sibling com_ids | **yes** | asw bridge missing -> get's read of x races |
| mp-comid-mismatch-nonsc | sibling com_ids, atomic data | no | **non-SC** — stale x allowed, race-free |

The pairing is the point: matching (or comparable ancestor/descendant) com_ids
reproduce the original ordering (race-free, SC); incomparable *sibling* com_ids
drop the asw synchronization between the flag's writer and reader, giving a data
race for ordinary data (mp-comid-mismatch-race) or a non-SC stale read for atomic
data (mp-comid-mismatch-nonsc).

## Why asw is the pivotal relation

For asw both endpoints are observable, so condition (2) does not apply; the gate
reduces to "both synchronizing ops >= c". A valid c (a common descendant of the
two ops' com_ids) exists exactly when those com_ids are comparable. Hence a
producer/consumer com_id mismatch (siblings) removes the cross-PE asw bridge,
while rdo (fence-triggered) and lco (blocking-op-triggered) still form within each
PE — leaving no common com_id to join them across the missing bridge.

# Summary of expected behaviors

### Part A — canonical families

**SC** = race-free and the weak outcome is forbidden; **non-SC** = race-free but
the weak outcome is allowed; **racy** = a data race exists. The api-only reference
per family is marked *(ref)*.

| Test | Family | Data race? | SC verdict | Note |
|---|---|---|---|---|
| mp-all-api *(ref)* | MP | no | **SC** | x always delivered |
| mp-partial-normal-data | MP | no | **SC** (retained) | normal data + API sync |
| mp-race-nofence | MP | **yes** | racy | fence removed |
| mp-race-remote-sync | MP | **yes** | racy | remote sync kills lco |
| sb-all-api-relaxed *(ref)* | SB | no | **non-SC** | no SC ref exists; weak allowed |
| sb-all-api-fence | SB | no | **non-SC** | fence insufficient for SB |
| sb-race-normal | SB | **yes** | racy | normal accesses |
| lb-all-api-relaxed | LB | no | **non-SC** | weak allowed |
| lb-all-api-sc *(ref)* | LB | no | **SC** | fence suffices for LB |
| lb-race-normal | LB | **yes** | racy | normal accesses |
| iriw-all-api-relaxed *(ref)* | IRIW | no | **non-SC** | no SC ref exists; weak allowed |
| iriw-all-api-fence | IRIW | no | **non-SC** | fence insufficient for IRIW |
| iriw-race-normal | IRIW | **yes** | racy | normal accesses |
| wrc-all-api *(ref)* | WRC | no | **SC** | causality holds |
| wrc-relaxed | WRC | no | **non-SC** | fences removed, causality broken |
| wrc-race-normal | WRC | **yes** | racy | normal accesses |
| rwc-all-api *(ref)* | RWC | no | **SC** | = WRC in this model |
| rwc-relaxed | RWC | no | **non-SC** | fences removed |
| rwc-race-normal | RWC | **yes** | racy | normal accesses |
| coww-all-api *(ref)* | CoWW | no | **SC** (coherent) | reads fence-ordered |
| coww-relaxed | CoWW | no | **non-coherent** | reads unordered |
| coww-race-normal | CoWW | **yes** | racy | normal accesses |
| isa2-all-api *(ref)* | ISA2 | no | **SC** | transitive sync composes |
| isa2-relaxed | ISA2 | no | **non-SC** | fences removed |
| isa2-race-normal | ISA2 | **yes** | racy | normal accesses |

### Part B — relation tests (`api_relations/`)

| Test | Relation exercised | Data race? |
|---|---|---|
| ilv/ilv-put-reads-local-store | ilv | no |
| ilv/ilv-get-overwrites-local-store | ilv (+lco) | no |
| ilv/ilv-local-load-before-get-store | ilv | no |
| lco/lco-put-store-after-src | lco | no |
| lco/lco-get-load-after-dst | lco | no |
| lco/lco-put-nbi-store-race | lco relaxed (nbi) | **yes** |
| lco/lco-get-nbi-load-race | lco relaxed (nbi) | **yes** |
| rdo/remote-store-fence-flag | rdo(i) w/ remote normal store | no |
| rdo/rdo-put-fence-put | rdo(ii) | no (2nd put wins) |
| rdo/rdo-put-put-race | rdo absent | **yes** (write-write) |
| rdo/rdo-put-fence-get-load | rdo(ii)+lco | no |
| rdo/rdo-put-get-load-race | rdo absent | **yes** |
| rdo/rdo-fence-orders-store-local-sync | rdo(i)+asw+lco | no |
| rdo/rdo-fence-orders-store-remote-sync | lco local-only | **yes** |
| rdo/rdo-nofence-store-local-sync-race | rdo absent | **yes** |
| rco/rco-quiet-orders-put-cross-pe | rco (case 4) | no |
| rco/rco-fence-insufficient-cross-pe-race | rco relaxed to fence | **yes** |
| asw/put-fence-flag | asw (+rdo+lco) | no |
| asw/mp-nonsync-flag-race | asw absent | **yes** |

## Cross-cutting findings

1. **SB and IRIW cannot be made SC by any OpenSHMEM primitive** — they need a
   store->load / multi-copy-atomic (from-read) cycle that is not part of
   `api_hb`, and the spec's simplified axioms omit SC.
2. **LB, WRC, RWC, CoWW, and ISA2 are all restored by `shmem_fence`** — their
   forbidden outcomes correspond to cycles/chains that close within `api_hb` via
   rdo + asw, and asw + rdo compose transitively (ISA2 across two sync hops).
3. **lco is local-only** — synchronizing through a *remote* read (atomic_fetch on
   another PE) does not order a subsequent access; that requires a quiet (rco).
4. **A fence only orders same-target-PE deliveries** (rdo case ii); ordering
   deliveries to *different* PEs requires a quiet/barrier (rco).
5. **Remote atomics are OpenSHMEM's relaxed atomics** — atomic (race-free) but
   with no ilv/lco/rdo, enabling non-SC-but-race-free executions (SB/LB/IRIW
   relaxed).
