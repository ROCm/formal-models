# OpenSHMEM API-relation litmus tests

Targeted litmus tests for the OpenSHMEM API-level memory model
(`llvm/openshmem_*.als`), organized by the API-level ordering relation each one
primarily exercises. Each test hand-encodes an execution and checks that the
intended outcome is satisfiable (SAT) and forbidden alternatives are
unsatisfiable (UNSAT). All open `openshmem_predicates_c11` (the spec's C++/C11
axioms); most are also valid under the LLVM-based `openshmem_predicates`.

Run one with:
```
build/jdk-17.0.10+7/bin/java -jar build/org.alloytools.alloy.dist.jar \
    exec -f -o build/temp/t llvm/test/openshmem/api_relations/<rel>/<name>.als
```

For the classic weak-memory families (MP, SB, LB, IRIW, WRC, RWC, CoWW, ISA2)
see `../canonical/`.

## The API-level relations

- **ilv** (implicit local visibility): a local observable access sees prior
  hb-ordered accesses of the initiating PE.
- **lco** (local completion order): a *blocking* op's *local* observable
  accesses complete before subsequent hb-ordered events of the caller.
  **Local-only.**
- **rdo** (remote delivery order, `shmem_fence`): case (i) a prior memory access
  is ordered before a later op's observable accesses; case (ii) two
  fence-separated observable accesses **to the same target PE** are ordered.
- **rco** (remote completion order, `shmem_quiet`/barrier): *full* connectivity
  across the operation, including across *different* target PEs.
- **asw** (API synchronizes-with): an observable write of a synchronizing op
  (AMO / signal / p2p-sync / lock) synchronizes with the observable read that
  reads from it.

Convention: `a@PEk` is object `a`'s copy on PE k.

## Directory layout

Each relation has a subdirectory. Where a relaxation of the ordering yields a
data race (or otherwise weaker behavior), a companion `*-race`/relaxed test sits
alongside the race-free base test.

### ilv/
- **ilv-put-reads-local-store** — a local store then a put reading the same local
  source: the put must read the store. No race.
- **ilv-get-overwrites-local-store** — a local store then a get writing the same
  local address: a later read sees the get's value. No race.
- **ilv-local-load-before-get-store** — a local load then a get writing the same
  local address: the load cannot read the get's store. No race.

  (ilv is an unconditional guarantee for local accesses, so it has no meaningful
  race relaxation without changing the test's meaning.)

### lco/
- **lco-put-store-after-src** — a blocking put then a local store to its source:
  the put's source-load completes first. No race.
- **lco-get-load-after-dst** — a blocking get then a local load of its dest: the
  get's local store completes first. No race.
- **lco-put-nbi-store-race** *(relaxation)* — the put made NON-BLOCKING: lco no
  longer applies, so the source-load races with the later store. **Race.**
- **lco-get-nbi-load-race** *(relaxation)* — the get made NON-BLOCKING: the local
  load races with the get's store. **Race.**

### rdo/
- **remote-store-fence-flag** — MP where the payload is delivered by a direct
  remote store (normal access), exercising rdo case (i). No race.
- **rdo-put-fence-put** — two puts to the same remote address across a fence: rdo
  case (ii) orders them, second wins. No race.
- **rdo-put-put-race** *(relaxation)* — same two puts, no fence: unordered
  conflicting writes. **Write-write race.**
- **rdo-put-fence-get-load** — put; fence; get reading it back; local load: an
  ordered copy chain. No race.
- **rdo-put-get-load-race** *(relaxation)* — same chain, no fence: the get's read
  races with the put. **Race.**
- **rdo-fence-orders-store-local-sync** — a fence orders a prior normal store
  before an atomic_set, delivered through a local wait. No race.
- **rdo-fence-orders-store-remote-sync** — same, but sync via a remote
  atomic_fetch: lco is local-only, so the subsequent remote get is not ordered.
  **Race.**
- **rdo-nofence-store-local-sync-race** *(relaxation)* — the local-sync version
  with the fence removed. **Race.**

### rco/
- **rco-quiet-orders-put-cross-pe** — a quiet orders a put (to PE1) before an
  atomic_set (to PE2) across PEs, which a fence cannot. No race.
- **rco-fence-insufficient-cross-pe-race** *(relaxation)* — the quiet replaced by
  a fence: rdo case (ii) cannot order accesses to *different* target PEs, so the
  consumer's get races with the put. **Race.**

### asw/
- **put-fence-flag** — canonical MP: put delivers data, fenced atomic_set raises
  the flag, a waiter consumes it. The atomic flag supplies asw. No race.
- **mp-nonsync-flag-race** *(relaxation)* — the flag raised/consumed with
  non-atomic (non-synchronizing) accesses: no asw is formed, so nothing orders
  the delivery before the consumer's read. **Race** (no race-free execution).

## Summary

| Test | Relation | Race? |
|---|---|---|
| ilv-put-reads-local-store | ilv | no |
| ilv-get-overwrites-local-store | ilv | no |
| ilv-local-load-before-get-store | ilv | no |
| lco-put-store-after-src | lco | no |
| lco-get-load-after-dst | lco | no |
| lco-put-nbi-store-race | lco (nbi) | **yes** |
| lco-get-nbi-load-race | lco (nbi) | **yes** |
| remote-store-fence-flag | rdo(i) | no |
| rdo-put-fence-put | rdo(ii) | no |
| rdo-put-put-race | rdo absent | **yes** |
| rdo-put-fence-get-load | rdo(ii)+lco | no |
| rdo-put-get-load-race | rdo absent | **yes** |
| rdo-fence-orders-store-local-sync | rdo(i)+asw+lco | no |
| rdo-fence-orders-store-remote-sync | lco local-only | **yes** |
| rdo-nofence-store-local-sync-race | rdo absent | **yes** |
| rco-quiet-orders-put-cross-pe | rco (case 4) | no |
| rco-fence-insufficient-cross-pe-race | rco relaxed to fence | **yes** |
| put-fence-flag | asw (+rdo+lco) | no |
| mp-nonsync-flag-race | asw absent | **yes** |
