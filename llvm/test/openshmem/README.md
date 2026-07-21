# OpenSHMEM API-level litmus tests

Litmus tests for the OpenSHMEM API-level memory model extension
(`llvm/openshmem_*.als`). Each test hand-encodes an execution and checks that
the intended outcome is satisfiable (SAT) and that the forbidden outcome is
unsatisfiable (UNSAT). All tests open `openshmem_predicates_c11` (the spec's
C++/C11 axioms); most are flavor-independent and also pass under the LLVM-based
`openshmem_predicates` (noted per test).

Run one with:
```
build/jdk-17.0.10+7/bin/java -jar build/org.alloytools.alloy.dist.jar \
    exec -f -o build/temp/t -s sat4j -t none -r 1 -q \
    llvm/test/openshmem/<name>.als
```

## API-level ordering relations exercised
- **ilv** (implicit local visibility): a local observable access sees prior
  hb-ordered accesses from the initiating PE.
- **lco** (local completion order): a blocking op's local observable accesses
  complete before subsequent hb-ordered events from the caller.
- **rdo** (remote delivery order): a fence orders accesses across it (case i:
  a prior memory access before a later op's observable accesses; case ii:
  fence-separated observable accesses to the *same* PE).
- **rco** (remote completion order): a quiet/barrier gives *full* connectivity
  across it (any PE), which a fence cannot.
- **asw** (API synchronizes-with): an observable write of an atomic/signaling/
  p2p-sync/lock op synchronizes with the observable read that reads from it.

Convention below: `a@PEk` is object `a`'s copy on PE k.

---

## Message passing (foundational; rdo + asw + lco)

### put-fence-flag
Canonical MP: a put delivers data, a fenced atomic_set raises a flag, a waiter
consumes it and reads the data.
```
PE0: shmem_put(dest=data, src, pe1)      # ST data@PE1
     shmem_fence()
     shmem_atomic_set(flag, 1, pe1)       # ST flag@PE1 (atomic)
PE1: shmem_wait_until(flag == 1)          # LD flag@PE1 (atomic)
     x = data                             # LD data@PE1
```
Chain: `put.ST(data) --rdo--> set.ST(flag) --asw--> wait.LD(flag) --lco--> load`.
Checks: good_outcome SAT; stale_read_impossible UNSAT; racy_without_sync SAT.

### remote-store-fence-flag
Same as above, but PE0 delivers the payload with a *direct remote store* through
a `shmem_ptr`-style pointer (a normal access targeting a remote PE), exercising
rdo case (i) with a normal access.
```
PE0: *ptr_to_PE1_data = 1                 # normal ST, home=PE0, target=PE1
     shmem_fence()
     shmem_atomic_set(flag, 1, pe1)
PE1: shmem_wait_until(flag == 1)
     x = data                             # LD data@PE1
```
Checks: remote_normal_access_ok SAT; good_outcome SAT; stale_read_impossible
UNSAT; racy_without_sync SAT.

---

## ilv — implicit local visibility

### ilv-put-reads-local-store
A local store then a put reading the same local source: the put must read the
store.
```
PE0: source = 1                           # ST source@PE0
     shmem_put(dest, source, pe1)         # LD source@PE0 ; ST dest@PE1
```
`ilv`: `store --> put.LD(source)`. Checks: put_reads_local_store SAT;
put_cannot_read_init UNSAT.

### ilv-get-overwrites-local-store
A local store then a get writing the same local address: the get's store
overwrites, so a later read sees the get's value.
```
PE0: dest = 1                             # ST dest@PE0
     shmem_get(dest, source, pe1)         # LD source@PE1 ; ST dest@PE0
     x = dest                             # LD dest@PE0
```
`ilv`: `store --> get.ST(dest)`; `lco`: `get.ST(dest) --> load`. Checks:
final_state_is_get SAT; final_state_not_store UNSAT. (Downstream-reader form, so
flavor-independent.)

### ilv-local-load-before-get-store
A local load then a get writing the same local address: the load is ordered
before the get's store and cannot read it.
```
PE0: x = dest                             # LD dest@PE0
     shmem_get(dest, source, pe1)         # LD source@PE1 ; ST dest@PE0
```
`ilv`: `load --> get.ST(dest)`. Checks: load_reads_pre_get_value SAT;
load_cannot_read_get UNSAT.

---

## lco — local completion order

### lco-put-store-after-src
A blocking put then a local store to its source: the put's source-load completes
before the later store overwrites the buffer.
```
PE0: shmem_put(dest, source, pe1)         # LD source@PE0 ; ST dest@PE1
     source = 1                           # ST source@PE0
```
`lco`: `put.LD(source) --> store`. Checks: put_load_reads_original SAT;
put_load_cannot_read_later_store UNSAT.

### lco-get-load-after-dst
A blocking get then a local load of its destination: the get's local store
completes before the later load.
```
PE0: shmem_get(dest, source, pe1)         # LD source@PE1 ; ST dest@PE0
     x = dest                             # LD dest@PE0
```
`lco`: `get.ST(dest) --> load`. Checks: get_load_reads_get_store SAT;
get_load_cannot_read_init UNSAT.

---

## rdo — remote delivery order (fence)

### rdo-put-fence-put
Two puts to the same remote address separated by a fence: rdo case (ii) orders
them (same target PE), so the second put wins.
```
PE0: shmem_put(a, b, pe1)                 # ST a@PE1
     shmem_fence()
     shmem_put(a, c, pe1)                 # ST a@PE1
```
Checks: writes_always_ordered UNSAT (never unordered); final_is_c SAT;
c_not_overwritten UNSAT. No race on PE1:a.

### rdo-put-put-race
Same two puts with no fence: unordered conflicting writes -> data race on PE1:a.
```
PE0: shmem_put(a, b, pe1)                 # ST a@PE1
     shmem_put(a, c, pe1)                 # ST a@PE1
```
Checks: data_race_on_a SAT (writes left unordered by api_hb); first_put_can_win
SAT. (Write-write race, detected structurally, not via DataRaceRead.)

### rdo-put-fence-get-load
A put then (after a fence) a get reading it back, then a local load: an ordered
copy chain a -> PE1:b -> PE0:c -> read.
```
PE0: shmem_put(b, a, pe1)                 # LD a@PE0 ; ST b@PE1
     shmem_fence()
     shmem_get(c, b, pe1)                 # LD b@PE1 ; ST c@PE0
     x = c                                # LD c@PE0
```
`rdo`: `put.ST(b) --> get.LD(b)`; `lco`: `get.ST(c) --> load`. Checks:
ordered_chain_exists SAT; get_reads_delivered_b UNSAT; final_load_reads_delivered_c
UNSAT. Flavor-independent.

### rdo-put-get-load-race
Same copy chain with no fence: the get's read of PE1:b races with the put's
store.
```
PE0: shmem_put(b, a, pe1)                 # LD a@PE0 ; ST b@PE1
     shmem_get(c, b, pe1)                 # LD b@PE1 ; ST c@PE0
     x = c
```
Checks: race_on_b SAT (get's LD of b@PE1 is a DataRaceRead). Flavor-independent.

### rdo-fence-orders-store-local-sync
Shows a fence ordering a prior *normal* store (rdo case i) before an atomic_set,
delivered transitively through a *local* wait.
```
PE0: a = 1                                # normal ST a@PE0
     shmem_fence()
     shmem_atomic_set(b, 1, pe1)          # ST b@PE1 (atomic)
PE1: shmem_wait_until(b == 1)             # LD b@PE1 (atomic, local)
     shmem_get(a, a, pe0)                 # LD a@PE0 ; ST a@PE1
     x = a                                # LD a@PE1
```
Chain: `st_a0 --rdo(i)--> set.ST(b) --asw--> wait.LD(b) --lco--> get.LD(a)`.
Checks: good_outcome SAT; get_reads_pe0_store UNSAT; final_load_returns_stored
UNSAT. No race; final load returns 1.

### rdo-fence-orders-store-remote-sync  (FINDING: races)
Same as above, but synchronization goes through a *remote* atomic_fetch of a
flag on PE2. This is a **data race**: lco (which carried the ordering above) is
local-only, so the remote fetch does not order the subsequent remote get.
```
PE0: a = 1
     shmem_fence()
     shmem_atomic_set(b, 1, pe2)          # ST b@PE2 (atomic)
PE1: r = shmem_atomic_fetch(b, pe2)       # LD b@PE2 (atomic, REMOTE)
     shmem_get(a, a, pe0)                 # LD a@PE0 ; ST a@PE1
     x = a
```
Checks: no_racefree_delivery UNSAT; get_read_races SAT. (Ordering the subsequent
remote get would require a quiet/barrier -> rco, not a fence.)

### rdo-nofence-store-local-sync-race
The local-sync version with the fence removed: without rdo, the prior normal
store is not ordered before the atomic_set -> data race on PE0:a.
```
PE0: a = 1
     shmem_atomic_set(b, 1, pe1)          # NO fence
PE1: shmem_wait_until(b == 1)
     shmem_get(a, a, pe0)
     x = a
```
Checks: race_on_a SAT; no_racefree_delivery UNSAT.

---

## rco — remote completion order (quiet/barrier)

### rco-quiet-orders-put-cross-pe
A quiet establishes cross-PE completion ordering that a fence could not: the
put's store (PE1) and the atomic_set's store (PE2) target *different* PEs, so
rdo case (ii) cannot order them; rco (full connectivity) can.
```
PE0: a = 1                                # normal ST a@PE0
     shmem_put(b, a, pe1)                 # LD a@PE0 ; ST b@PE1
     shmem_quiet()
     shmem_atomic_set(c, 1, pe2)          # ST c@PE2 (atomic)
PE2: shmem_wait_until(c == 1)             # LD c@PE2 (atomic, local)
     shmem_get(d, b, pe1)                 # LD b@PE1 ; ST d@PE2
```
Chain: `st_a0 --ilv--> put.LD(a)`, `put.ST(b) --rco(case4)--> set.ST(c)
--asw--> wait.LD(c) --lco--> get.LD(b)`. Checks: good_outcome SAT;
get_loads_put_not_stale UNSAT; put_loaded_local_store UNSAT. No race; the get is
guaranteed to load the put's value. Flavor-independent.

---

## Summary

| Test | Focus | Result |
|---|---|---|
| put-fence-flag | rdo+asw+lco | race-free MP |
| remote-store-fence-flag | rdo(i) w/ remote normal store | race-free MP |
| ilv-put-reads-local-store | ilv | no race |
| ilv-get-overwrites-local-store | ilv (+lco) | no race |
| ilv-local-load-before-get-store | ilv | no race |
| lco-put-store-after-src | lco | no race |
| lco-get-load-after-dst | lco | no race |
| rdo-put-fence-put | rdo(ii) | no race, 2nd put wins |
| rdo-put-put-race | rdo absent | race |
| rdo-put-fence-get-load | rdo(ii)+lco | no race |
| rdo-put-get-load-race | rdo absent | race |
| rdo-fence-orders-store-local-sync | rdo(i)+asw+lco | no race |
| rdo-fence-orders-store-remote-sync | lco local-only | race |
| rdo-nofence-store-local-sync-race | rdo absent | race |
| rco-quiet-orders-put-cross-pe | rco (case 4) | no race |
