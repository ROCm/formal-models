# OpenSHMEM API-level litmus tests

Litmus tests for the OpenSHMEM API-level memory-model extension
(`llvm/openshmem_*.als`). Each test hand-encodes an execution and checks that the
intended outcome is satisfiable (SAT) and forbidden alternatives are
unsatisfiable (UNSAT). All open `openshmem_predicates_c11` (the spec's C++/C11
axioms) unless noted; most also pass under the LLVM-based `openshmem_predicates`.

Run one with:
```
build/jdk-17.0.10+7/bin/java -jar build/org.alloytools.alloy.dist.jar \
    exec -f -o build/temp/t llvm/test/openshmem/<path>.als
```

## Layout

- **`canonical/`** — the classic weak-memory litmus families (MP, SB, LB, IRIW,
  WRC, RWC, CoWW, ISA2). Each family has an all-API race-free version,
  relaxation variants (remote-atomic / no-fence), and a normal-access race
  version. See the per-family details (pseudocode, expected outcome, reasoning)
  in the full report `openshmem_litmus_tests_report.md` in this directory.
- **`api_relations/`** — targeted tests organized by the API-level ordering
  relation each exercises (`ilv/`, `lco/`, `rdo/`, `rco/`, `asw/`), each with
  relaxation/race variants where meaningful. See `api_relations/README.md`.
- **`notation/`** — the same tests expressed in the gentest DSL (work in
  progress; gated out of llvm-lit via `lit.local.cfg`).

## The API-level ordering relations

- **ilv** (implicit local visibility): a local observable access sees prior
  hb-ordered accesses of the initiating PE.
- **lco** (local completion order): a *blocking* op's *local* observable accesses
  complete before subsequent hb-ordered events of the caller. Local-only.
- **rdo** (remote delivery order, `shmem_fence`): case (i) a prior memory access
  before a later op's observable accesses; case (ii) fence-separated observable
  accesses to the *same* target PE.
- **rco** (remote completion order, `shmem_quiet`/barrier): full connectivity
  across the operation, including across *different* target PEs.
- **asw** (API synchronizes-with): an observable write of a synchronizing op
  (AMO / signal / p2p-sync / lock) synchronizes with the observable read that
  reads from it.

A **remote atomic** access (target PE != home PE) is atomic (cannot race) but
earns no ilv/lco/rdo — the OpenSHMEM analog of a relaxed atomic.
