module memory_consistency/llvm/test/openshmem/canonical/mp/comid/mp_comid_mismatch_nonsc

// MP with com_id, MISMATCHING case with ATOMIC data: like mp-comid-mismatch-race
// but the data x is delivered and read with atomic operations, so the broken
// synchronization yields NON-SC behavior (a stale read) rather than a data race.
//
// Producer (C_prod) and consumer (C_cons) are incomparable sibling com_ids, so
// the asw bridge st_flag [C_prod] -> ld_flag [C_cons] does not form (asw needs
// the writer and reader ops to share a com_id). The producer fence gives
// st_x --rdo--> st_flag (at C_prod) and the consumer fence gives
// ld_flag --rdo--> ld_x (at C_cons), but with no common com_id and no asw bridge
// there is no st_x --> ld_x path. Because every access is atomic there is no data
// race, but the consumer's atomic read of x may observe the stale initial value
// even after observing the flag: the weak (non-SC) outcome is ALLOWED.
//
//   PE0: atomic_set(x,1,pe1)   [C_prod] ; fence [C_prod] ; atomic_set(flag,1,pe1) [C_prod]
//   PE1: r0=atomic_fetch(flag,pe1) [C_cons] ; fence [C_cons] ; r1=atomic_fetch(x,pe1) [C_cons]
//
// With a single shared com_id the chain st_x --rdo--> st_flag --asw--> ld_flag
// --rdo--> ld_x forms and the weak outcome is forbidden (SC); the mismatch is
// what admits it.

open memory_consistency/llvm/openshmem_comid

one sig PE0, PE1 extends PE {}

one sig op_setx, op_fence0, op_setf extends Operation {}    // PE0
one sig op_fetchf, op_fence1, op_fetchx extends Operation {} // PE1

one sig st_x    extends SimpleWrite {}   // atomic_set x@PE1 (atomic)
one sig st_flag extends SimpleWrite {}   // atomic_set flag@PE1 (atomic)
one sig ld_flag extends SimpleRead {}    // atomic_fetch flag@PE1 (atomic)
one sig ld_x    extends SimpleRead {}    // atomic_fetch x@PE1 (atomic)

one sig Init_x_pe1    extends Init {}
one sig Init_flag_pe1 extends Init {}

// --- com_id: producer and consumer in incomparable sibling com_ids ---
one sig C_prod, C_cons extends ComId {}
fact comids {
  C_prod.com_parent = GlobalComId
  C_cons.com_parent = GlobalComId
  C_prod.tagged = op_setx + op_fence0 + op_setf   // producer
  C_cons.tagged = op_fetchf + op_fence1 + op_fetchx // consumer
  no GlobalComId.tagged
}

fact program {
  po_imm = op_setx -> op_fence0 + op_fence0 -> op_setf
         + op_fetchf -> op_fence1 + op_fence1 -> op_fetchx

  issues = op_setx -> st_x + op_setf -> st_flag
         + op_fetchf -> ld_flag + op_fetchx -> ld_x
  no op_sb

  AmoOp = op_setx + op_setf + op_fetchf + op_fetchx
  FenceOp = op_fence0 + op_fence1
  no PutOp and no GetOp
  no P2PSyncOp and no PutSignalOp and no SignalFetchOp
  no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  PE1.target_of = st_x + ld_x + st_flag + ld_flag + Init_x_pe1 + Init_flag_pe1

  PE0.home_of = op_setx + op_fence0 + op_setf
  PE1.home_of = op_fetchf + op_fence1 + op_fetchx + Init_x_pe1 + Init_flag_pe1

  same_location =
      (Init_x_pe1 + st_x + ld_x) -> (Init_x_pe1 + st_x + ld_x) +
      (Init_flag_pe1 + st_flag + ld_flag) -> (Init_flag_pe1 + st_flag + ld_flag)
}

fact atomicity {
  st_x + st_flag + ld_flag + ld_x in Monotonic
  no (st_x + st_flag + ld_flag + ld_x) & (Release + Acquire)
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// 1. Non-SC outcome ALLOWED: even after observing the flag, the atomic read of x
//    may see the stale initial value. Race-free (all accesses atomic).
run weak_outcome_allowed {
  openshmem_comid_memory_model
  (st_flag -> ld_flag) in rf
  (Init_x_pe1 -> ld_x) in rf
  no_api_races_comid
} for 0 but 16 Event, exactly 3 ComId expect 1

// 2. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_comid_memory_model
  not no_api_races_comid
} for 0 but 16 Event, exactly 3 ComId expect 0
