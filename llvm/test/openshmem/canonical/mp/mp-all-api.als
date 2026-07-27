module memory_consistency/llvm/test/openshmem/canonical/mp/mp_all_api

// Canonical MP (message passing), realized entirely with OpenSHMEM API calls.
//
// Classic MP:  P0: x = 1 ; release(flag = 1)      P1: r0 = acquire(flag) ; r1 = x
// Forbidden weak outcome: r0 == 1 && r1 == 0 (sees the flag but not x).
//
// OpenSHMEM realization (all accesses are API calls):
//   PE0: shmem_put(x, xsrc, pe1)          // deliver x to PE1     (LD xsrc@PE0 ; ST x@PE1)
//        shmem_fence()                     // order delivery before the flag
//        shmem_atomic_set(flag, 1, pe1)    // release flag        (ST flag@PE1)
//   PE1: shmem_wait_until(flag == 1)       // acquire flag        (LD flag@PE1, local)
//        shmem_get(r, x, pe1)              // read x (local self-get; LD x@PE1 ; ST r@PE1)
//
// Ordering chain that forbids the weak outcome:
//   put.ST(x@PE1) --rdo--> set.ST(flag@PE1) --asw--> wait.LD(flag@PE1) --lco--> get.LD(x@PE1)
// so once the flag is observed, the get's read of x must observe the put. Race-free.

open memory_consistency/llvm/openshmem_predicates_c11

one sig PE0, PE1 extends PE {}

one sig op_put, op_fence, op_set extends Operation {}   // PE0
one sig op_wait, op_rget extends Operation {}           // PE1

one sig ld_xsrc extends SimpleRead {}   // put: LD xsrc@PE0 (local source)
one sig st_x    extends SimpleWrite {}  // put: ST x@PE1 (remote dest)
one sig st_flag extends SimpleWrite {}  // atomic_set: ST flag@PE1 (atomic)
one sig ld_flag extends SimpleRead {}   // wait_until: LD flag@PE1 (atomic, local)
one sig ld_x    extends SimpleRead {}   // get: LD x@PE1 (local source of self-get)
one sig st_r    extends SimpleWrite {}  // get: ST r@PE1 (local dest)

one sig Init_xsrc_pe0 extends Init {}
one sig Init_x_pe1    extends Init {}
one sig Init_flag_pe1 extends Init {}
one sig Init_r_pe1    extends Init {}

fact program {
  po_imm = op_put -> op_fence + op_fence -> op_set + op_wait -> op_rget

  issues = op_put -> ld_xsrc + op_put -> st_x
         + op_set -> st_flag
         + op_wait -> ld_flag
         + op_rget -> ld_x + op_rget -> st_r
  op_sb  = op_put -> (ld_xsrc -> st_x) + op_rget -> (ld_x -> st_r)

  PutOp = op_put
  FenceOp = op_fence
  AmoOp = op_set
  P2PSyncOp = op_wait
  GetOp = op_rget
  no PutSignalOp and no SignalFetchOp and no QuietOp and no BarrierOp and no LockOp
  no NonBlocking and no NoStore
}

fact locations_and_pes {
  PE0.target_of = ld_xsrc + Init_xsrc_pe0
  PE1.target_of = st_x + st_flag + ld_flag + ld_x + st_r
                  + Init_x_pe1 + Init_flag_pe1 + Init_r_pe1

  PE0.home_of = op_put + op_fence + op_set + Init_xsrc_pe0
  PE1.home_of = op_wait + op_rget + Init_x_pe1 + Init_flag_pe1 + Init_r_pe1

  same_location =
      (Init_xsrc_pe0 + ld_xsrc) -> (Init_xsrc_pe0 + ld_xsrc) +
      (Init_x_pe1 + st_x + ld_x) -> (Init_x_pe1 + st_x + ld_x) +
      (Init_flag_pe1 + st_flag + ld_flag) -> (Init_flag_pe1 + st_flag + ld_flag) +
      (Init_r_pe1 + st_r) -> (Init_r_pe1 + st_r)
}

fact atomicity {
  st_flag + ld_flag in Monotonic
  no (st_flag + ld_flag) & (Release + Acquire)
  no (ld_xsrc + st_x + ld_x + st_r) & Atomic
}

fact scopes_flat {
  all e : Event - Init | e.execscope_instance = System
  all a : Atomic - Init | a.syncscope_instance = System
}

// --- Checks (given the flag is observed) ---

// 1. Expected behavior is satisfiable: the get reads the put's x, race-free.
run can_read_put {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) in rf
  no_api_races
} for 0 but 16 Event expect 1

// 2. No alternative: the forbidden outcome (flag seen but x stale) is impossible.
run cannot_read_stale_x {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  (st_x -> ld_x) not in rf
} for 0 but 16 Event expect 0

// 3. No data race in any legal execution where the flag is observed.
run no_data_race {
  openshmem_memory_model
  (st_flag -> ld_flag) in rf
  not no_api_races
} for 0 but 16 Event expect 0
