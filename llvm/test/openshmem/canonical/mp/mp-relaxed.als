module memory_consistency/llvm/test/openshmem/canonical/mp/mp_relaxed

// Canonical MP, race-free but NON-SC variant. Unlike mp-race-nofence (which drops
// the fence with ORDINARY put/get data and therefore races), this keeps every
// access ATOMIC -- the data x is delivered with shmem_atomic_set and read with
// shmem_atomic_fetch -- and simply omits the fence between the two producer
// stores. Being atomic there is no data race, but with no fence nothing orders
// the store of x before the store of the flag, so the consumer can observe the
// flag yet still read the stale initial x: the weak MP outcome is ALLOWED
// (race-free, non-SC).
//
//   PE0: shmem_atomic_set(x, 1, pe1)       // ST x@PE1 (atomic)   <-- was put; fence removed
//        shmem_atomic_set(flag, 1, pe1)    // ST flag@PE1 (atomic)
//   PE1: shmem_wait_until(flag == 1)       // LD flag@PE1 (atomic, local)
//        r1 = shmem_atomic_fetch(x, pe1)   // LD x@PE1 (atomic)   <-- was get
//
// The consumer side is still ordered (asw on the flag + lco after the blocking
// wait: st_flag --asw--> ld_flag --lco--> ld_x); it is the missing producer fence
// (no rdo st_x --> st_flag) that admits the stale read. Re-inserting a fence
// between the two producer atomic_sets would restore SC.

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_setx, op_setf extends Operation {}   // PE0
one sig op_wait, op_fetchx extends Operation {} // PE1

one sig st_x    extends SimpleWrite {}   // atomic_set x@PE1 (atomic)
one sig st_flag extends SimpleWrite {}   // atomic_set flag@PE1 (atomic)
one sig ld_flag extends SimpleRead {}    // wait_until flag@PE1 (atomic, local)
one sig ld_x    extends SimpleRead {}    // atomic_fetch x@PE1 (atomic)

one sig Init_x_pe1    extends Init {}
one sig Init_flag_pe1 extends Init {}

fact program {
  po_imm = op_setx -> op_setf + op_wait -> op_fetchx

  issues = op_setx -> st_x + op_setf -> st_flag
         + op_wait -> ld_flag + op_fetchx -> ld_x
  no op_sb

  AmoOp = op_setx + op_setf + op_fetchx
  P2PSyncOp = op_wait
  no PutOp and no GetOp and no FenceOp
  no PutSignalOp and no SignalFetchOp and no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  no PE0.target_of
  PE1.target_of = st_x + ld_x + st_flag + ld_flag + Init_x_pe1 + Init_flag_pe1

  PE0.home_of = op_setx + op_setf
  PE1.home_of = op_wait + op_fetchx + Init_x_pe1 + Init_flag_pe1

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
//    may see the stale initial value (no fence -> no rdo ordering st_x before the
//    flag). Race-free (all accesses atomic).
run weak_outcome_allowed {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  (Init_x_pe1 -> ld_x) in rf
  no_api_races
} for 0 but 16 Event expect 1

// 2. Every execution is race-free (all accesses are atomic).
run no_data_race {
  openshmem_memory_model
  not no_api_races
} for 0 but 16 Event expect 0
