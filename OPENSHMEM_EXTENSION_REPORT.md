# OpenSHMEM API-level memory model — formal-models (in-house LLVM Alloy) extension

## Status: implemented and **validated under Alloy 6.2.0**

New files (additive; no base modules edited):
- `llvm/openshmem_events.als` — Step 1 (PEs, per-(addr,PE) locations, operation events) and Step 2 (observable accesses, `issues`, program-order exemption, `op_sb`).
- `llvm/openshmem_predicates.als` — Step 3 (ilv/lco/rdo/rco/asw) and Step 5 (`api_hb`, api-retargeted happens-before / data-race / coherence axioms).
- `llvm/openshmem_model.als` — top-level model fact + Step 4 (fused collectives) design note.
- `llvm/test/openshmem/put-fence-flag.als` — worked litmus test (put → fence → atomic_set / wait_until → load).
- `llvm/test/openshmem/remote-store-fence-flag.als` — litmus test exercising a normal (non-observable) access that targets a *remote* PE (direct store via shmem_ptr), ordered through rdo → asw → lco.

### Spec-revision note: remote normal accesses
The `openshmem_home_pe` fact previously forced every normal (non-observable)
access to target its home PE (`a.target_pe = a.home_pe`), i.e. local-only. This
was relaxed so a normal thread access may target a *remote* PE (e.g. a direct
load/store through a pointer from `shmem_ptr`/`shmem_team_ptr`); its home PE is
still the issuing thread's PE (via the `po in home_pe.~home_pe` grouping), only
`target_pe` is now free. Init writes remain local (`i.target_pe = i.home_pe`).
No relation logic needed to change — `ilv/lco/rdo/rco` are phrased over
`target_pe`/`home_pe` comparisons and handle remote accesses correctly (a remote
normal access is naturally excluded from `ilv`'s local-visibility clause and
included as an ordinary "memory access" in `rdo`/`rco`).

Run it:
```
build/jdk-17.0.10+7/bin/java -jar build/org.alloytools.alloy.dist.jar \
    exec -f -o build/temp/osh -s sat4j -t none -r 1 -q \
    llvm/test/openshmem/put-fence-flag.als
```
Result: `good_outcome_exists` SAT, `stale_read_impossible` UNSAT, `racy_without_sync` SAT — the API `api_hb` chain `put.ST(data@PE1) --rdo--> set.ST(flag@PE1) --asw--> wait.LD(flag@PE1) --lco--> load(data@PE1)` forbids the stale read, while the control confirms the result is non-vacuous.

(Note: Alloy 6.2.0 needs Java 17; the system default is Java 8, so a Temurin JDK 17 was fetched into `build/jdk-17.0.10+7`.)

## How the base represents the model
- `po = ^po_imm` is sb; `Access` carries `same_location` (an equivalence abstracting the location); `Write` carries `mo`, `rf`; `Fence` and the `Monotonic/Release/Acquire/SeqCst` subset sigs give memory orders.
- `llvm_hb = ^(po_imm + llvm_sw) + initializes_before`; races and coherence are defined over `llvm_hb` in `llvm_predicates.als`. Scopes (`scopes.als`) add a `ScopeInstance` tree and `compatible_scope`.

## Mapping of the five steps
1. **PEs + operation events (easy).** Added `sig PE` with `target_of`/`home_of` (mirroring the scopes.als pattern of putting relations on the auxiliary sig so base modules stay untouched). Crucially, requiring `same_location in same_pe` makes every `same_location` class a distinct (addr, PE) pair — so the base coherence/mo/rf machinery is per-(addr,PE) *for free*. `Operation extends Event` participates in `po` but, being neither `Access` nor `Fence`, never enters `mo/rf/sw`.
2. **Observable accesses (medium).** `issues : Operation -> Access`; program-order exemption via `no observable_accesses <: po_imm` and `no po_imm :> observable_accesses`. Intra-op dependencies live in a separate `op_sb` (kept out of `po`).
3. **API relations (hard — the crux, but a natural fit for Alloy's relational algebra).** `ilv/lco/rdo/rco/asw` are defined directly over `llvm_hb`, `issues`, and `target_pe`. Note: the spec's `asw` definition transposes its A/B labels relative to its own worked example; implemented as write→read (matching PL `sw` orientation and the example).
4. **Fused collectives (hardest — partial/design).** A single event spanning N PEs collides with the base invariant `lone E.~po_imm`. Design (in `openshmem_model.als`): keep one op per PE + a `fused_with` equivalence, and have `rco` quantify over the class (`hb ; fused_with`, `fused_with ; hb`). Not wired in; barrier currently reasoned per-PE.
5. **api_hb + axioms (medium).** `api_hb = ^(pl_hb + op_sb + ilv + lco + rdo + rco + asw)`. The key realization: you **cannot** just call `llvm_memory_model` and add relations, because its data-race/`may_see` logic is hard-wired to `llvm_hb` and would flag API-ordered accesses as PL races. So `api_happens_before` re-states `may_see`/data-race over `api_hb` (a copy-and-retarget of ~15 lines), plus a coherence axiom `irreflexive((rf^-1)?;mo;rf?;api_hb)`.

## Integration difficulty: **3/5**
Additive layering works cleanly for steps 1–3 and 5 — no base file needed editing. The two real frictions are: (a) the base coherence/data-race predicates are phrased over `llvm_hb`/`same_location`, forcing a retargeted copy rather than pure reuse; and (b) fused collectives vs the per-thread total-order invariant. Reusing `same_location` as the (addr,PE) identity was the single biggest simplification.

## Deferred / future work
- Wire `fused_with` into `rco` and add barrier/reduction litmus tests.
- Reuse/retarget `llvm_seqcst_impl` over `api_hb` (only minimal mo-coherence is included now).
- Extend RMW atomicity to `sb_amo`-linked observable AMO accesses.
- A `ShmemTest` gentest subclass to auto-expand `shmem_*` calls into observable accesses (the litmus is currently hand-written).
- Contexts/teams/atomicity-domains and the NOSTORE gate beyond the single `NoStore` flag.
