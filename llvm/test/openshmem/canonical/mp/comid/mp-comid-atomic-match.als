module memory_consistency/llvm/test/openshmem/canonical/mp/comid/mp_comid_atomic_match

// MP with com_id, ATOMIC data, MATCHING case: same program as
// mp-comid-mismatch-nonsc.als (data x delivered/read atomically, a fence on each
// PE) but every operation carries the SAME com_id C1. The chain
//   st_x --rdo--> st_flag --asw--> ld_flag --rdo--> ld_x
// now forms at c = C1, so the weak (stale-x) outcome is FORBIDDEN (SC). This is
// the matched reference that mp-comid-mismatch-nonsc relaxes: swapping to two
// incomparable com_ids is exactly what admits the non-SC outcome.
//
//   PE0: atomic_set(x,1,pe1) [C1] ; fence [C1] ; atomic_set(flag,1,pe1) [C1]
//   PE1: r0=atomic_fetch(flag,pe1) [C1] ; fence [C1] ; r1=atomic_fetch(x,pe1) [C1]

open memory_consistency/llvm/openshmem_comid

one sig PE0, PE1 extends PE {}

one sig op_setx, op_fence0, op_setf extends Operation {}    // PE0
one sig op_fetchf, op_fence1, op_fetchx extends Operation {} // PE1

one sig st_x    extends SimpleWrite {}
one sig st_flag extends SimpleWrite {}
one sig ld_flag extends SimpleRead {}
one sig ld_x    extends SimpleRead {}

one sig Init_x_pe1    extends Init {}
one sig Init_flag_pe1 extends Init {}

// --- com_id: one shared non-global id C1 tagging every operation ---
one sig C1 extends ComId {}
fact comids {
  C1.com_parent = GlobalComId
  C1.tagged = op_setx + op_fence0 + op_setf + op_fetchf + op_fence1 + op_fetchx
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

// 1. Expected: after observing the flag, the read of x observes the put, race-free.
run can_observe_x {
  openshmem_comid_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) in rf
  no_api_races_comid
} for 0 but 16 Event, exactly 2 ComId expect 1

// 2. SC retained (matching com_ids): the stale-x (weak) outcome is FORBIDDEN.
run weak_outcome_forbidden {
  openshmem_comid_memory_model
  (st_flag -> ld_flag) in rf
  (Init_x_pe1 -> ld_x) in rf
} for 0 but 16 Event, exactly 2 ComId expect 0

// 3. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_comid_memory_model
  not no_api_races_comid
} for 0 but 16 Event, exactly 2 ComId expect 0
