# MP litmus variants with com_id

These tests exercise the OPTIONAL communication-identifier (`com_id`) extension of
the OpenSHMEM API-level model (`llvm/openshmem_comid.als`). They open
`openshmem_comid` and use `openshmem_comid_memory_model` / `no_api_races_comid`
instead of the base model. The plain (no-com_id) MP tests live in the parent
directory.

## The com_id extension in one paragraph

Every access and operation carries a `com_id`; observable accesses inherit their
operation's com_id, and an untagged event defaults to the global com_id (the top
of a parent/child hierarchy, greater than every other com_id). Each API relation
(ilv/lco/rdo/rco/asw) is considered *per com_id*: an edge is established at
relation-com_id `c` only if (1) the triggering operation(s) have com_id `>= c`,
and (2) any *non-observable access* endpoint has com_id `<= c`. Observable-access
endpoints are exempt from (2) — they are covered by (1) through their issuing
operation. `api_hb` is the union over `c` of the transitive closures of the
c-gated relations together with `sw` and preserved program order (`ppo`). Because
each com_id is closed separately, a happens-before path built from API relations
must thread through a single common com_id.

## Variants and results (all validated)

| File | com_ids | Data race? | Outcome |
|---|---|---|---|
| mp-comid-match | one shared C1 | no | **SC** — get can't read stale x (recovers plain MP) |
| mp-comid-parent-child | producer child, consumer parent (comparable) | no | **SC** — comparable com_ids still synchronize |
| mp-comid-mismatch-race | producer C_prod, consumer C_cons (sibling) | **yes** | asw bridge missing -> get's read of x races |
| mp-comid-atomic-match | one shared C1 (atomic data) | no | **SC** — stale-x outcome forbidden |
| mp-comid-mismatch-nonsc | C_prod / C_cons (atomic data) | no | **non-SC** — stale-x outcome allowed, race-free |

The pairing is the point: with **matching or comparable** (ancestor/descendant)
com_ids the behavior is identical to the plain model (race-free, SC); with
**incomparable sibling** com_ids the producer's flag write and the consumer's flag
read no longer synchronize, which breaks the delivery chain — yielding a data race
when the data is ordinary, or a non-SC stale read when the data is atomic.

## Why asw is the pivotal relation here

asw has two observable endpoints, so gate condition (2) does not apply to them;
the gate reduces to "both synchronizing ops `>= c`". A valid `c` — a common
descendant of the two ops' com_ids — exists exactly when those com_ids are
**comparable** (equal, or ancestor/descendant). Hence asw synchronizes the flag's
writer and reader iff their ops' com_ids are comparable, and fails only for
incomparable siblings. rdo (triggered by the fence) and lco (triggered by the
blocking op) still form within each PE, but for a sibling mismatch there is no
common com_id to join them across the missing asw bridge.
