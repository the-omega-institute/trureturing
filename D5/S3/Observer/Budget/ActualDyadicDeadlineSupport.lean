/- GID: D5/S3/Observer/Budget/ActualDyadicDeadlineSupport
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/ActualDyadicDeadlineSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical dyadic deadline support preserves acquired histories and raw clock parity. -/

import D5.S3.ConceptDynamics.Coding.ActualDyadicCausalPrefixRepairCapacity
import D5.S3.Observer.Budget.DyadicDeadlineStaircase

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Observer.Budget.ActualDyadicDeadlineSupport
open D5.S3.ConceptDynamics.Coding.ActualDyadicCausalPrefixRepairCapacity
open D5.S3.Observer.Budget.DyadicForwardWaitingOptimality

private theorem rawSensor_eq_rawBit {P : Nat} (positive : 0 < P)
    (b : Fin 2) (r : Fin P) (N : Nat) :
    rawSensor positive b r N = rawBit P b N r.val := by
  apply Fin.ext
  change ((b.val * P + r.val + N) % (2 * P)) / P = _
  rw [Nat.mul_comm 2 P]
  exact Nat.mod_mul_right_div_self _ _ _

/-- Every newly appended read lies between the starting and reporting clocks. -/
theorem execution_read_bounds {P : Nat} (positive : 0 < P) (b : Fin 2)
    (policy : Record → Action P) (r : Fin P)
    (start : Record) (word : List (Fin 2)) (terminal : Record × Fin P)
    (run : Execution positive b policy r start word terminal) :
    start.events ≤ terminal.1.events ∧
    ∃ trace, terminal.1.reads = start.reads ++ trace ∧
      trace.length = word.length ∧
      (∀ item ∈ trace, start.events ≤ item.1 ∧ item.1 ≤ terminal.1.events) ∧
      trace.Pairwise (fun x y => x.1 ≤ y.1) := by
  induction run with
  | @stopped record output choice =>
      refine ⟨le_rfl, [], ?_, rfl, ?_, ?_⟩
      · simp only [List.append_nil]
      · simp only [List.not_mem_nil, false_implies, forall_const]
      · exact List.Pairwise.nil
  | @advanced record word terminal choice rest ih =>
      obtain ⟨mono, trace, shape, length, bounds, order⟩ := ih
      refine ⟨by simp only at mono; omega, trace, shape, length, ?_, order⟩
      intro item member
      have h := bounds item member
      simp only at h
      exact ⟨by omega, h.2⟩
  | @queried record word terminal choice rest ih =>
      obtain ⟨mono, trace, shape, length, bounds, order⟩ := ih
      refine ⟨mono, (record.events, rawSensor positive b r record.events) :: trace,
        ?_, ?_, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using shape
      · simp only [List.length_cons, length]
      · intro item member
        rcases List.mem_cons.mp member with eq | member
        · subst item; exact ⟨le_rfl, mono⟩
        · exact bounds item member
      · apply List.pairwise_cons.mpr
        exact ⟨fun item member => (bounds item member).1, order⟩

private def drive {P : Nat} (positive : 0 < P) :
    {d : Nat} → Protocol d → Nat → List (Nat × Fin 2) → Nat → Action P
  | _, .stop answer, _, _, _ => .stop ⟨answer % P, Nat.mod_lt _ positive⟩
  | _, .query wait next, now, [], event =>
      if event < now + wait then .advance else .read
  | _, .query wait next, now, (_, bit) :: tail, event =>
      drive positive (next bit) (now + wait) tail event

private theorem advance_to {P : Nat} (positive : 0 < P) (b : Fin 2)
    (policy : Record → Action P) (r : Fin P) (wait : Nat) :
    ∀ (now : Nat) (past : List (Nat × Fin 2)) (word : List (Fin 2))
      (terminal : Record × Fin P),
      (∀ k, now ≤ k → k < now + wait → policy ⟨k, past⟩ = .advance) →
      Execution positive b policy r ⟨now + wait, past⟩ word terminal →
      Execution positive b policy r ⟨now, past⟩ word terminal := by
  induction wait with
  | zero => intro now past word terminal choices rest; simpa only [Nat.add_zero] using rest
  | succ wait ih =>
      intro now past word terminal choices rest
      apply Execution.advanced (choices now le_rfl (by omega))
      apply ih (now + 1) past word terminal
      · intro k lower upper; apply choices k (by omega) (by omega)
      · convert rest using 1 <;> congr 1 <;> omega

/-- Only finite wait/read tree behavior needed by the source is transported. -/
private theorem protocol_primitive_realization {P : Nat} (positive : 0 < P) (b : Fin 2)
    {d : Nat} (p : Protocol d) (policy : Record → Action P) :
    ∀ (now : Nat) (past : List (Nat × Fin 2)),
      (∀ tail event, policy ⟨event, past ++ tail⟩ = drive positive p now tail event) →
      ∀ r : Fin P, ∃ word terminal,
        Execution positive b policy r ⟨now, past⟩ word terminal ∧
        word.length ≤ d ∧
        terminal.2.val = (execute (rawBit P b) p now r.val).1 % P ∧
        terminal.1.events = (execute (rawBit P b) p now r.val).2 ∧
        (word = [] → terminal.1.events = now) ∧
        (word ≠ [] → ∃ before bit, terminal.1.reads = before ++ [(terminal.1.events, bit)]) := by
  induction p with
  | @stop d answer =>
      intro now past alignment r
      refine ⟨[], (⟨now, past⟩, ⟨answer % P, Nat.mod_lt _ positive⟩), ?_, ?_, rfl, rfl, (fun _ => rfl), ?_⟩
      · apply Execution.stopped
        simpa only [List.append_nil, drive] using alignment [] now
      · simp only [List.length_nil, Nat.zero_le]
      · intro nonempty; exact False.elim (nonempty rfl)
  | @query d wait next ih =>
      intro now past alignment r
      let N := now + wait
      let bit := rawSensor positive b r N
      have childAlignment : ∀ tail event,
          policy ⟨event, (past ++ [(N, bit)]) ++ tail⟩ =
            drive positive (next bit) N tail event := by
        intro tail event
        simpa only [List.append_assoc, List.singleton_append, drive, N] using
          alignment ((N, bit) :: tail) event
      obtain ⟨word, terminal, run, bounded, answer, clock, emptyClock, lastRead⟩ :=
        ih bit N (past ++ [(N, bit)]) childAlignment r
      refine ⟨bit :: word, terminal, ?_, by simpa using Nat.succ_le_succ bounded, ?_, ?_, ?_, ?_⟩
      · apply advance_to positive b policy r wait now past (bit :: word) terminal
        · intro k lower upper
          simpa only [List.append_nil, drive, if_pos upper] using alignment [] k
        · apply Execution.queried
          · simpa only [List.append_nil, drive, N, lt_self_iff_false, if_false] using alignment [] N
          · exact run
      · simpa only [execute, bit, rawSensor_eq_rawBit, N] using answer
      · simpa only [execute, bit, rawSensor_eq_rawBit, N] using clock
      · intro impossible; cases impossible
      · intro _
        by_cases empty : word = []
        · obtain ⟨_, trace, shape, len, _, _⟩ := execution_read_bounds positive b policy r _ _ _ run
          have nil : trace = [] := List.eq_nil_of_length_eq_zero (by simpa only [empty, List.length_nil] using len)
          refine ⟨past, bit, ?_⟩
          rw [shape, nil, List.append_nil, emptyClock empty]
        · exact lastRead empty

private theorem forced_trace_midpoint_lower {P : Nat} (positive : 0 < P)
    (b : Fin 2) (r : Fin P) (d : Nat) :
    ∀ (lo early N : Nat) (bit : Fin 2) (past : List (Nat × Fin 2)),
      lo + 2 ^ (d + 1) ≤ P → lo ≤ r.val → r.val < lo + 2 ^ (d + 1) →
      ForcedReadTrace b r lo (d + 1) (past ++ [(N, bit)]) →
      (past ++ [(N, bit)]).Pairwise (fun x y => x.1 ≤ y.1) →
      (∀ item ∈ past ++ [(N, bit)], early ≤ item.1) →
      (execute (threshold P) (midpoint P (d + 1) lo early) early r.val).2 ≤ N := by
  have first_phase (early actual w : Nat) (hw : w < P)
      (hbefore : early ≤ actual) (hphase : (early + w) % P = actual % P) :
      early + w ≤ actual := by
    by_contra hn
    have hlt : actual < early + w := by omega
    have hcong : actual ≡ early + w [MOD P] := hphase.symm
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add (Nat.le_of_lt hlt)).mp hcong
    have kpos : 1 ≤ k := by
      by_contra hz
      have zero : k = 0 := by omega
      simp only [zero, Nat.mul_zero, Nat.add_zero] at hk
      omega
    have prod := Nat.mul_le_mul_left P kpos
    simp only [mul_one] at prod
    omega
  have phase (lo early k : Nat) (hi : lo + 2 ^ (k + 1) ≤ P) :
      (early + (P - (lo + 2 ^ k) + P - early % P) % P) % P = P - (lo + 2 ^ k) := by
    have hp := Nat.two_pow_pos k
    have he : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
    have hn := Nat.mod_lt early positive
    have hm : 0 < lo + 2 ^ k ∧ lo + 2 ^ k < P := by omega
    have hmod : (P - (lo + 2 ^ k) + P - early % P) + early % P = P - (lo + 2 ^ k) + P := by omega
    rw [Nat.add_mod, Nat.add_mod_mod, Nat.add_comm, Nat.mod_add_mod,
      hmod, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  induction d with
  | zero =>
      intro lo early N bit past within lower upper forced order after
      obtain ⟨M, v, tail, shape, actualPhase, value, rest⟩ := forced
      change tail = [] at rest
      subst tail
      have len := congrArg List.length shape
      simp only [List.length_append, List.length_cons, List.length_nil] at len
      have nil : past = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst past
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq, and_true] at shape
      obtain ⟨rfl, rfl⟩ := shape
      let w := (P - (lo + 1) + P - early % P) % P
      have minimum := first_phase early N w (Nat.mod_lt _ positive)
        (after (N, bit) (by simp)) (by simpa only [w, pow_zero] using (phase lo early 0 within).trans actualPhase.symm)
      simpa only [D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.midpoint, execute, pow_zero, w] using minimum
  | succ d ih =>
      intro lo early N bit past within lower upper forced order after
      obtain ⟨M, v, tail, shape, actualPhase, value, rest⟩ := forced
      have tailNonempty : tail ≠ [] := by
        intro nil; rw [nil] at rest
        obtain ⟨_, _, _, impossible, _, _, _⟩ := rest
        cases impossible
      cases past with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at shape
          exact False.elim (tailNonempty shape.2.symm)
      | cons first past =>
          simp only [List.cons_append, List.cons.injEq] at shape
          have tailShape : tail = past ++ [(N, bit)] := shape.2.symm
          simp only [List.cons_append, shape.1] at order after
          have pairwise := List.pairwise_cons.mp order
          let w := (P - (lo + 2 ^ (d + 1)) + P - early % P) % P
          have minimum := first_phase early M w (Nat.mod_lt _ positive)
            (after (M, v) (by simp))
            (by simpa only [w] using (phase lo early (d + 1) within).trans actualPhase.symm)
          have read : threshold P (early + w) r.val =
              if r.val < lo + 2 ^ (d + 1) then 0 else 1 := by
            unfold threshold
            rw [phase lo early (d + 1) within]
            have half : lo + 2 ^ (d + 1) ≤ P := by
              have he : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by
                rw [pow_succ]; omega
              omega
            rw [Nat.sub_sub_self half]
          change (execute (threshold P) (midpoint P (d + 1)
            (if threshold P (early + w) r.val = 0 then lo else lo + 2 ^ (d + 1))
            (early + w)) (early + w) r.val).2 ≤ N
          rw [read]
          have he : 2 ^ (d + 1 + 1) = 2 * 2 ^ (d + 1) := by rw [pow_succ]; omega
          by_cases low : r.val < lo + 2 ^ (d + 1)
          · rw [if_pos low, if_pos rfl]
            apply ih lo (early + w) N bit past (by omega) lower low
            · simpa only [if_pos low, Nat.zero_mul, Nat.add_zero, tailShape] using rest
            · exact pairwise.2
            · intro item member
              have h := pairwise.1 item member
              change M ≤ item.1 at h
              omega
          · rw [if_neg low, if_neg (by decide : (1 : Fin 2) ≠ 0)]
            apply ih (lo + 2 ^ (d + 1)) (early + w) N bit past (by omega) (by omega) (by omega)
            · simpa only [if_neg low, Nat.one_mul, tailShape] using rest
            · exact pairwise.2
            · intro item member
              have h := pairwise.1 item member
              change M ≤ item.1 at h
              omega


theorem deadline_allowed_primitive_realization (d : Nat) (b : Fin 2)
    (D t u K : Nat)
    (deadline : D5.S3.Observer.Budget.DyadicForwardWaitingOptimality.sharpWait (d + 1) ≤ D)
    (prefixBound : t < 2 ^ d) (lastBit : u < 2)
    (allowed : D5.S3.Observer.Budget.DyadicPrefixDelayRange.earliestTime d t +
      2 ^ (d + 1) * K ≤ D) :
    let P := 2 ^ (d + 1)
    ∃ policy : Record → Action P,
      (∀ r : Fin P, ∃ word terminal,
        Execution (Nat.two_pow_pos (d + 1)) b policy r ⟨0, []⟩ word terminal ∧
        word.length ≤ d + 1 ∧ terminal.2 = r ∧ terminal.1.events ≤ D) ∧
      ∃ (r : Fin P) (word : List (Fin 2)) (terminal : Record × Fin P)
        (before : List (Nat × Fin 2)) (bit : Fin 2),
        r.val = 2 * t + u ∧
        Execution (Nat.two_pow_pos (d + 1)) b policy r ⟨0, []⟩ word terminal ∧
        word.length ≤ d + 1 ∧ terminal.2 = r ∧
        terminal.1.events = D5.S3.Observer.Budget.DyadicPrefixDelayRange.earliestTime d t + P * K ∧
        terminal.1.reads = before ++ [(terminal.1.events, bit)] := by
  dsimp only
  let P := 2 ^ (d + 1)
  have positive : 0 < P := Nat.two_pow_pos (d + 1)
  have sourceBound : 2 * t + u < P := by
    dsimp [P]; rw [pow_succ]; omega
  obtain ⟨p, family, time⟩ :=
    ((D5.S3.Observer.Budget.DyadicPrefixDelayRange.deadline_prefix_time_range_and_collision d b D).1.2
      deadline t u K prefixBound lastBit).mpr allowed
  let policy : Record → Action P := fun record => drive positive p 0 record.reads record.events
  have alignment : ∀ tail event, policy ⟨event, [] ++ tail⟩ = drive positive p 0 tail event := by
    intro tail event; rfl
  have runs (r : Fin P) := protocol_primitive_realization positive b p policy 0 [] alignment r
  have correct (r : Fin P) : (execute (rawBit P b) p 0 r.val).1 = r.val :=
    family.1 r.val (Nat.zero_le _) (by simpa only [Nat.zero_add] using r.isLt)
  have success : ∀ r : Fin P, ∃ word terminal,
      Execution positive b policy r ⟨0, []⟩ word terminal ∧
        word.length ≤ d + 1 ∧ terminal.2 = r := by
    intro r
    obtain ⟨word, terminal, run, bound, answer, clock, rest⟩ := runs r
    refine ⟨word, terminal, run, bound, ?_⟩
    apply Fin.ext
    rw [correct r, Nat.mod_eq_of_lt r.isLt] at answer
    exact answer
  refine ⟨policy, ?_, ?_⟩
  · intro r
    obtain ⟨word, terminal, run, bound, answer, clock, rest⟩ := runs r
    refine ⟨word, terminal, run, bound, ?_, ?_⟩
    · apply Fin.ext
      rw [correct r, Nat.mod_eq_of_lt r.isLt] at answer
      exact answer
    · rw [clock]; exact family.2 r.val r.isLt
  · let r : Fin P := ⟨2 * t + u, sourceBound⟩
    obtain ⟨word, terminal, run, bound, answer, clock, empty, last⟩ := runs r
    have saturated := (actual_continuation_capacity_and_saturation positive b policy
      ⟨0, []⟩ (d + 1) Finset.univ (by
        intro s _; exact success s)).2 (by simp only [Finset.card_univ, Fintype.card_fin]; rfl)
      r (Finset.mem_univ _) word terminal run bound
    have nonempty : word ≠ [] := by intro nil; rw [nil, List.length_nil] at saturated; omega
    obtain ⟨before, bit, shape⟩ := last nonempty
    refine ⟨r, word, terminal, before, bit, rfl, run, bound, ?_, ?_, shape⟩
    · apply Fin.ext
      rw [correct r, Nat.mod_eq_of_lt r.isLt] at answer
      exact answer
    · rw [clock]; exact time

theorem actual_final_time_normal_form {P : Nat} (positive : 0 < P)
    (d : Nat) (power : P = 2 ^ (d + 1)) (b : Fin 2) (policy : Record → Action P)
    (success : ∀ r : Fin P, ∃ word terminal,
      Execution positive b policy r ⟨0, []⟩ word terminal ∧ word.length ≤ d + 1 ∧ terminal.2 = r)
    (r : Fin P) (word : List (Fin 2)) (terminal : Record × Fin P)
    (run : Execution positive b policy r ⟨0, []⟩ word terminal) (bound : word.length ≤ d + 1) :
    ∃ past N bit K,
      past.length = d ∧ acquiredPrefix (P := P) b past 0 = r.val / 2 ∧
      terminal.1.reads = past ++ [(N, bit)] ∧
      ReachedRecord positive b policy r ⟨0, []⟩ ⟨N, past⟩ ∧ policy ⟨N, past⟩ = .read ∧
      bit.val = (b.val + N / P + r.val % 2) % 2 ∧
      N = D5.S3.Observer.Budget.DyadicPrefixDelayRange.earliestTime d (r.val / 2) + P * K ∧
      N ≤ terminal.1.events := by
  obtain ⟨past, N, bit, bit', len, len', pastLen, acquired, shape, shape',
    reached, reached', phase, raw, raw', choice, rest, rest'⟩ :=
    actual_acquired_prefix_and_final_query positive d power b policy success r r rfl
      word word terminal terminal run run bound bound
  obtain ⟨trace, traceShape, forced⟩ := actual_dyadic_interval_trace positive b policy
    ⟨0, []⟩ 0 (d + 1) (by rw [power]; omega)
    (by intro s _ _; exact success s) r (Nat.zero_le _) (by rw [← power]; simpa using r.isLt)
    word terminal run bound
  simp only [List.nil_append] at traceShape
  have traceEq : trace = past ++ [(N, bit)] := traceShape.symm.trans shape
  rw [traceEq] at forced
  obtain ⟨_, physical, physicalShape, _, bounds, order⟩ := execution_read_bounds positive b policy r _ _ _ run
  simp only [List.nil_append] at physicalShape
  have physicalEq : physical = past ++ [(N, bit)] := physicalShape.symm.trans shape
  rw [physicalEq] at bounds order
  have lower := forced_trace_midpoint_lower positive b r d 0 0 N bit past
    (by rw [power]; omega) (Nat.zero_le _) (by rw [← power]; simpa using r.isLt)
    forced order (by intro item _; exact Nat.zero_le _)
  let t := r.val / 2
  let u := r.val % 2
  have tBound : t < 2 ^ d := by
    have hr : r.val < 2 ^ (d + 1) := by simpa only [power] using r.isLt
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; omega
    dsimp [t]; omega
  have uBound : u < 2 := Nat.mod_lt _ (by decide)
  have sourceEq : 2 * t + u = r.val := by dsimp [t,u]; omega
  have law : ∀ n, sensor P b n r.val = threshold P n r.val := by
    intro n
    subst P
    exact (dyadic_forward_waiting_optimality (d + 1) b).1 n r.val r.isLt |>.2
  have congrRead : ∀ {k} (p : Protocol k) now,
      execute (sensor P b) p now r.val = execute (threshold P) p now r.val := by
    intro k p
    induction p with
    | stop answer => intro now; rfl
    | query wait next ih => intro now; simp only [execute, law]; exact ih _ _
  have early := (D5.S3.Observer.Budget.TerminalClockCompression.earliest_midpoint_terminal_time
    d b t u tBound uBound).1
  rw [sourceEq] at early
  change (execute (rawBit (2 ^ (d + 1)) b) (rawMidpoint (2 ^ (d + 1)) b (d + 1)) 0 r.val).2 = _ at early
  rw [← power] at early
  rw [rawMidpoint, (transport_execute P b (midpoint P (d + 1) 0 0) 0 r.val).1,
    congrRead] at early
  have earliestLe : D5.S3.Observer.Budget.DyadicPrefixDelayRange.earliestTime d t ≤ N := by
    rw [early] at lower
    simpa only [D5.S3.Observer.Budget.DyadicPrefixDelayRange.earliestTime, ← power] using lower
  have small : 2 * t ≤ P - 1 := by have := r.isLt; dsimp [t]; omega
  have earliestEq : D5.S3.Observer.Budget.DyadicPrefixDelayRange.earliestTime d t =
      (P - 1 - 2 * t) + P * t.bitIndices.length := by
    unfold D5.S3.Observer.Budget.DyadicPrefixDelayRange.earliestTime
    rw [← power]; omega
  have divEq := Nat.mod_add_div N P
  have weightLe : t.bitIndices.length ≤ N / P := by
    by_contra no
    have hp := Nat.mul_le_mul_left P (show N / P + 1 ≤ t.bitIndices.length by omega)
    rw [Nat.mul_add, Nat.mul_one] at hp
    rw [earliestEq] at earliestLe
    change N % P = P - 1 - 2 * t at phase
    omega
  refine ⟨past, N, bit, N / P - t.bitIndices.length, pastLen, acquired, shape,
    reached, choice, raw, ?_, (bounds (N,bit) (by simp)).2⟩
  rw [earliestEq, Nat.mul_sub]
  change N % P = P - 1 - 2 * t at phase
  have hp := Nat.mul_le_mul_left P weightLe
  omega



open DyadicPrefixDelayRange

/-- A successful primitive run whose literal final read meets the deadline.
The reporting clock may be later than the final read. -/
def DeadlineObservation (d : Nat) (b : Fin 2) (D : Nat)
    (policy : Record → Action (2 ^ (d + 1))) (r : Fin (2 ^ (d + 1)))
    (past : List (Nat × Fin 2)) (N : Nat) (bit : Fin 2) : Prop :=
  ∃ word terminal,
    Execution (Nat.two_pow_pos (d + 1)) b policy r ⟨0, []⟩ word terminal ∧
    word.length ≤ d + 1 ∧ terminal.2 = r ∧
    terminal.1.reads = past ++ [(N, bit)] ∧ N ≤ D

/-- All sources have a correct run with at most d+1 reads, ending in a read under D. -/
def actualDeadlineFamily (d : Nat) (b : Fin 2) (D : Nat)
    (policy : Record → Action (2 ^ (d + 1))) : Prop :=
  ∀ r, ∃ past N bit, DeadlineObservation d b D policy r past N bit

/-- Supported times range over the entire primitive-policy deadline family. -/
def actualSupportedTime (d : Nat) (b : Fin 2) (D t N : Nat) : Prop :=
  ∃ policy, actualDeadlineFamily d b D policy ∧
    ∃ r past bit, r.val / 2 = t ∧ DeadlineObservation d b D policy r past N bit

private theorem family_success (d : Nat) (b : Fin 2) (D : Nat)
    (policy : Record → Action (2 ^ (d + 1)))
    (family : actualDeadlineFamily d b D policy) :
    ∀ r, ∃ word terminal,
      Execution (Nat.two_pow_pos (d + 1)) b policy r ⟨0, []⟩ word terminal ∧
      word.length ≤ d + 1 ∧ terminal.2 = r := by
  intro r
  obtain ⟨past, N, bit, word, terminal, run, bound, answer, _, _⟩ := family r
  exact ⟨word, terminal, run, bound, answer⟩

/-- The primitive record itself determines the prefix and raw final clock parity. -/
theorem actual_deadline_observation_normal_form (d : Nat) (b : Fin 2) (D : Nat)
    (policy : Record → Action (2 ^ (d + 1)))
    (family : actualDeadlineFamily d b D policy)
    (r : Fin (2 ^ (d + 1))) (past : List (Nat × Fin 2)) (N : Nat) (bit : Fin 2)
    (observation : DeadlineObservation d b D policy r past N bit) :
    past.length = d ∧ acquiredPrefix (P := 2 ^ (d + 1)) b past 0 = r.val / 2 ∧
    ReachedRecord (Nat.two_pow_pos (d + 1)) b policy r ⟨0, []⟩ ⟨N, past⟩ ∧
    policy ⟨N, past⟩ = .read ∧ bit.val = (b.val + N / 2 ^ (d + 1) + r.val % 2) % 2 ∧
    ∃ K, N = earliestTime d (r.val / 2) + 2 ^ (d + 1) * K := by
  obtain ⟨word, terminal, run, bound, _, shape, _⟩ := observation
  obtain ⟨past', N', bit', K, len, acquired, shape', reached, choice, raw, normal, _⟩ :=
    actual_final_time_normal_form (Nat.two_pow_pos (d + 1)) d rfl b policy
      (family_success d b D policy family) r word terminal run bound
  have last : (N', bit') = (N, bit) := by
    simpa using congrArg List.getLast? (shape'.symm.trans shape)
  have clock : N' = N := congrArg Prod.fst last
  have value : bit' = bit := congrArg Prod.snd last
  simp only [clock, value] at shape' reached choice raw normal
  have histEq : past' = past := by
    exact List.append_cancel_right (shape'.symm.trans shape)
  simp only [histEq] at acquired shape' reached choice raw normal
  rw [histEq] at len
  exact ⟨len, acquired, reached, choice, raw, K, normal⟩

/-- Every allowed final time is realized by one policy on both sibling sources,
with an identical reached pre-final history and the literal raw sensor bits. -/
theorem actual_deadline_pair_realization (d : Nat) (b : Fin 2) (D t K : Nat)
    (deadline : sharpWait (d + 1) ≤ D) (ht : t < 2 ^ d)
    (allowed : earliestTime d t + 2 ^ (d + 1) * K ≤ D) :
    let N := earliestTime d t + 2 ^ (d + 1) * K
    ∃ policy, actualDeadlineFamily d b D policy ∧
      ∃ past, past.length = d ∧ acquiredPrefix (P := 2 ^ (d + 1)) b past 0 = t ∧
        policy ⟨N, past⟩ = .read ∧
        ∀ u : Fin 2, ∃ (r : Fin (2 ^ (d + 1))) (bit : Fin 2),
          r.val = 2 * t + u.val ∧
          ReachedRecord (Nat.two_pow_pos (d + 1)) b policy r ⟨0, []⟩ ⟨N, past⟩ ∧
          bit.val = (b.val + N / 2 ^ (d + 1) + u.val) % 2 ∧
          DeadlineObservation d b D policy r past N bit := by
  dsimp only
  let P := 2 ^ (d + 1)
  let N := earliestTime d t + P * K
  obtain ⟨policy, all, r0, word0, terminal0, before0, bit0, source0, run0, bound0,
    answer0, clock0, reads0⟩ :=
    deadline_allowed_primitive_realization d b D t 0 K deadline ht (by decide) allowed
  have success : ∀ r : Fin P, ∃ word terminal,
      Execution (Nat.two_pow_pos (d + 1)) b policy r ⟨0, []⟩ word terminal ∧
      word.length ≤ d + 1 ∧ terminal.2 = r := by
    intro r; obtain ⟨word, terminal, run, bound, answer, _⟩ := all r
    exact ⟨word, terminal, run, bound, answer⟩
  have family : actualDeadlineFamily d b D policy := by
    intro r; obtain ⟨word, terminal, run, bound, answer, deadline⟩ := all r
    obtain ⟨past, N, bit, K, _, _, shape, _, _, _, _, clockBound⟩ :=
      actual_final_time_normal_form (Nat.two_pow_pos (d + 1)) d rfl b policy
        success r word terminal run bound
    exact ⟨past, N, bit, word, terminal, run, bound, answer, shape, clockBound.trans deadline⟩
  obtain ⟨past, N0, bit, K0, len, acquired, shape, reached, choice, raw, normal, _⟩ :=
    actual_final_time_normal_form (Nat.two_pow_pos (d + 1)) d rfl b policy
      success r0 word0 terminal0 run0 bound0
  have sameLast : (N0, bit) = (terminal0.1.events, bit0) := by
    simpa using congrArg List.getLast? (shape.symm.trans reads0)
  have sameClock : N0 = N := (congrArg Prod.fst sameLast).trans clock0
  have prefix0 : r0.val / 2 = t := by omega
  rw [sameClock] at shape reached choice raw
  refine ⟨policy, family, past, len, by simpa only [prefix0] using acquired, choice, ?_⟩
  intro u
  let r : Fin P := ⟨2 * t + u.val, by dsimp [P]; rw [pow_succ]; omega⟩
  obtain ⟨word, terminal, run, bound, answer, _⟩ := all r
  have pair : r0.val / 2 = r.val / 2 := by dsimp [r]; omega
  obtain ⟨past', N', v, v', _, _, len', acquired', shape0', shape', reached0', reached',
    phase', raw0', raw', choice', rest0', rest'⟩ :=
    actual_acquired_prefix_and_final_query (Nat.two_pow_pos (d + 1)) d rfl b policy
      success r0 r pair word0 word terminal0 terminal run0 run bound0 bound
  have last : (N', v) = (N, bit) := by
    simpa using congrArg List.getLast? (shape0'.symm.trans shape)
  have clk : N' = N := congrArg Prod.fst last
  have val : v = bit := congrArg Prod.snd last
  rw [clk, val] at shape0'
  rw [clk] at shape' reached' raw'
  have histEq : past' = past := List.append_cancel_right (shape0'.symm.trans shape)
  rw [histEq] at shape' reached'
  refine ⟨r, v', rfl, reached', ?_, word, terminal, run, bound, answer, shape', allowed⟩
  have mod : r.val % 2 = u.val := by dsimp [r]; omega
  simpa only [mod] using raw'

/-- Exactly the nonnegative whole-period delays of the physical earliest time
are supported by the all-source deadline family. -/
theorem actual_deadline_time_support (d : Nat) (b : Fin 2) (D t N : Nat)
    (deadline : sharpWait (d + 1) ≤ D) (ht : t < 2 ^ d) :
    actualSupportedTime d b D t N ↔
      ∃ K, N = earliestTime d t + 2 ^ (d + 1) * K ∧ N ≤ D := by
  constructor
  · rintro ⟨policy, family, r, past, bit, quotient, observation⟩
    obtain ⟨_, _, _, _, _, K, normal⟩ :=
      actual_deadline_observation_normal_form d b D policy family r past N bit observation
    obtain ⟨_, _, _, _, _, _, bound⟩ := observation
    exact ⟨K, by simpa only [quotient] using normal, bound⟩
  · rintro ⟨K, rfl, allowed⟩
    obtain ⟨policy, family, past, _, _, _, both⟩ :=
      actual_deadline_pair_realization d b D t K deadline ht allowed
    obtain ⟨r, bit, source, _, _, observation⟩ := both 0
    have quotient : r.val / 2 = t := by
      have source' : r.val = 2 * t := by simpa using source
      omega
    exact ⟨policy, family, r, past, bit, quotient, observation⟩
/-- Raw-Y uses quotient parity, rather than the parity of the added delay. -/
theorem actual_raw_clock_quotient (d t K : Nat) (ht : t < 2 ^ d) :
    (earliestTime d t + 2 ^ (d + 1) * K) / 2 ^ (d + 1) =
      t.bitIndices.length + K := by
  let P := 2 ^ (d + 1)
  have hp : 0 < P := Nat.two_pow_pos (d + 1)
  have small : 2 * t < P := by dsimp [P]; rw [pow_succ]; omega
  have shape : earliestTime d t = (P - 1 - 2 * t) + P * t.bitIndices.length := by
    dsimp [earliestTime, P]; omega
  change (earliestTime d t + P * K) / P = _
  rw [shape, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_div_left _ _ hp,
    Nat.div_eq_of_lt (show P - 1 - 2 * t < P by omega), Nat.zero_add]

private theorem earliest_le_sharp (d : Nat) (b : Fin 2) (t : Nat) (ht : t < 2 ^ d) :
    earliestTime d t ≤ sharpWait (d + 1) := by
  have sourceBound : 2 * t + 0 < 2 ^ (d + 1) := by rw [pow_succ]; omega
  have bound := (dyadic_forward_waiting_optimality (d + 1) b).2.2.2
    (2 * t + 0) sourceBound
  have time := (TerminalClockCompression.earliest_midpoint_terminal_time d b t 0 ht (by decide)).1
  change (execute (rawBit (2 ^ (d + 1)) b) (rawMidpoint (2 ^ (d + 1)) b (d + 1))
    0 (2 * t + 0)).2 = earliestTime d t at time
  rw [time] at bound
  exact bound

/-- Actual supported raw clock parities, over all realizing policies and histories. -/
noncomputable def actualParitySupport (d : Nat) (b : Fin 2) (D t : Nat) : Finset (Fin 2) := by
  classical
  exact Finset.univ.filter (fun nu => ∃ N,
    actualSupportedTime d b D t N ∧ N / 2 ^ (d + 1) % 2 = nu.val)

/-- A prefix has its earliest raw parity, and gains both parities exactly when
one additional whole period fits under the common deadline. -/
theorem actual_deadline_raw_parity_support (d : Nat) (b : Fin 2) (D t : Nat)
    (deadline : sharpWait (d + 1) ≤ D) (ht : t < 2 ^ d) (nu : Fin 2) :
    nu ∈ actualParitySupport d b D t ↔
      nu.val = t.bitIndices.length % 2 ∨ earliestTime d t + 2 ^ (d + 1) ≤ D := by
  classical
  have early : earliestTime d t ≤ D := (earliest_le_sharp d b t ht).trans deadline
  simp only [actualParitySupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨N, support, parity⟩
    obtain ⟨K, rfl, allowed⟩ := (actual_deadline_time_support d b D t N deadline ht).mp support
    rw [actual_raw_clock_quotient d t K ht] at parity
    by_cases zero : K = 0
    · left; simpa only [zero, Nat.add_zero] using parity.symm
    · right
      have mul := Nat.mul_le_mul_left (2 ^ (d + 1)) (show 1 ≤ K by omega)
      simp only [Nat.mul_one] at mul
      omega
  · intro permitted
    rcases permitted with same | extra
    · refine ⟨earliestTime d t, ?_, ?_⟩
      · apply (actual_deadline_time_support d b D t _ deadline ht).mpr
        exact ⟨0, by simp, early⟩
      · have eq := actual_raw_clock_quotient d t 0 ht
        simpa only [Nat.mul_zero, Nat.add_zero, same] using congrArg (· % 2) eq
    · let K := if nu.val = t.bitIndices.length % 2 then 0 else 1
      have kBound : K ≤ 1 := by dsimp [K]; split_ifs <;> omega
      have allowed : earliestTime d t + 2 ^ (d + 1) * K ≤ D := by
        have mul := Nat.mul_le_mul_left (2 ^ (d + 1)) kBound
        simp only [Nat.mul_one] at mul
        omega
      refine ⟨earliestTime d t + 2 ^ (d + 1) * K,
        (actual_deadline_time_support d b D t _ deadline ht).mpr ⟨K, rfl, allowed⟩, ?_⟩
      rw [actual_raw_clock_quotient d t K ht]
      have nuBound := nu.isLt
      dsimp [K]; split_ifs with same <;> omega

/-- The finite type set uses actual raw clock parity. -/
noncomputable def actualTypes (d : Nat) (b : Fin 2) (D : Nat) :
    Finset (Fin (2 ^ d) × Fin 2) := by
  classical
  exact Finset.univ.filter (fun x => x.2 ∈ actualParitySupport d b D x.1.val)

private theorem actual_types_card (d : Nat) (b : Fin 2) (D : Nat)
    (deadline : sharpWait (d + 1) ≤ D) :
    (actualTypes d b D).card = 2 ^ d + (eligiblePrefixes d D).card := by
  classical
  let base : Fin (2 ^ d) → Fin (2 ^ d) × Fin 2 := fun t =>
    (t, ⟨t.val.bitIndices.length % 2, Nat.mod_lt _ (by decide)⟩)
  let second : Fin (2 ^ d) → Fin (2 ^ d) × Fin 2 := fun t =>
    (t, ⟨(t.val.bitIndices.length + 1) % 2, Nat.mod_lt _ (by decide)⟩)
  have shape : actualTypes d b D = Finset.univ.image base ∪
      (eligiblePrefixes d D).image second := by
    ext x; rcases x with ⟨t, nu⟩
    simp only [actualTypes, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [actual_deadline_raw_parity_support d b D t.val deadline t.isLt nu]
    constructor
    · intro permitted
      by_cases same : nu.val = t.val.bitIndices.length % 2
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, Prod.ext rfl (Fin.ext same.symm)⟩
      · have extra : earliestTime d t.val + 2 ^ (d + 1) ≤ D := permitted.resolve_left same
        have opposite : (t.val.bitIndices.length + 1) % 2 = nu.val := by
          have := nu.isLt; omega
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, extra⟩,
          Prod.ext rfl (Fin.ext opposite)⟩
    · intro member
      rcases Finset.mem_union.mp member with first | last
      · obtain ⟨s, _, eq⟩ := Finset.mem_image.mp first
        have ts : s = t := congrArg Prod.fst eq
        subst s
        left
        exact (congrArg (fun x => x.2.val) eq).symm
      · obtain ⟨s, member, eq⟩ := Finset.mem_image.mp last
        have ts : s = t := congrArg Prod.fst eq
        subst s
        right
        exact (Finset.mem_filter.mp member).2
  have disjoint : Disjoint (Finset.univ.image base) ((eligiblePrefixes d D).image second) := by
    apply Finset.disjoint_left.mpr
    intro x first last
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp first
    obtain ⟨s, _, eq⟩ := Finset.mem_image.mp last
    have ts : s = t := congrArg Prod.fst eq
    subst s
    have bits := congrArg (fun x => x.2.val) eq
    dsimp [base, second] at bits
    omega
  have baseInj : Function.Injective base := by intro t s eq; exact congrArg Prod.fst eq
  have secondInj : Function.Injective second := by intro t s eq; exact congrArg Prod.fst eq
  rw [shape, Finset.card_union_of_disjoint disjoint,
    Finset.card_image_of_injective _ baseInj, Finset.card_image_of_injective _ secondInj]
  simp

/-- The exact dyadic staircase is transferred to primitive all-source schedules.
Singleton support has the earliest raw parity, including parity one. -/
theorem actual_deadline_staircase (d h : Nat) (b : Fin 2) :
    let D := sharpWait (d + 1) + h
    let q := (Finset.Icc 1 (d + 1)).filter (fun i => 2 ^ i ≤ h)
    (∀ t : Fin (2 ^ d), actualParitySupport d b D t.val =
      if t ∈ eligiblePrefixes d D then Finset.univ
      else {⟨t.val.bitIndices.length % 2, Nat.mod_lt _ (by decide)⟩}) ∧
    ((Finset.univ : Finset (Fin (2 ^ d))).filter
      (fun t => (actualParitySupport d b D t.val).card = 1)).card = d + 1 - q.card ∧
    (actualTypes d b D).card = 2 ^ (d + 1) - (d + 1) + q.card := by
  classical
  dsimp only
  let D := sharpWait (d + 1) + h
  let q := (Finset.Icc 1 (d + 1)).filter (fun i => 2 ^ i ≤ h)
  have deadline : sharpWait (d + 1) ≤ D := by dsimp [D]; omega
  have support (t : Fin (2 ^ d)) : actualParitySupport d b D t.val =
      if t ∈ eligiblePrefixes d D then Finset.univ
      else {⟨t.val.bitIndices.length % 2, Nat.mod_lt _ (by decide)⟩} := by
    ext nu
    rw [actual_deadline_raw_parity_support d b D t.val deadline t.isLt nu]
    by_cases extra : t ∈ eligiblePrefixes d D
    · have bound := (Finset.mem_filter.mp extra).2
      simp [extra, bound]
    · have bound : ¬ earliestTime d t.val + 2 ^ (d + 1) ≤ D := by
        simpa [eligiblePrefixes] using extra
      simp only [if_neg extra, Finset.mem_singleton]
      constructor
      · intro perm; exact Fin.ext (perm.resolve_right bound)
      · intro eq; left; exact congrArg Fin.val eq
  have counts : 2 ^ d + (eligiblePrefixes d D).card =
      2 ^ (d + 1) - (d + 1) + q.card := by
    have first := ((deadline_family_operational_capacity.{0} d b D).2 deadline).2.2
    have second := (DyadicDeadlineStaircase.deadline_family_closed_staircase.{0} d h b).2.2
    exact first.symm.trans second
  have singleShape : ((Finset.univ : Finset (Fin (2 ^ d))).filter
      (fun t => (actualParitySupport d b D t.val).card = 1)) =
      Finset.univ.filter (fun t => ¬ earliestTime d t.val + 2 ^ (d + 1) ≤ D) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, support t]
    by_cases extra : t ∈ eligiblePrefixes d D
    · have bound := (Finset.mem_filter.mp extra).2
      simp [extra, bound]
    · have bound : ¬ earliestTime d t.val + 2 ^ (d + 1) ≤ D := by
        simpa [eligiblePrefixes] using extra
      simp [extra, bound]
  have split := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 ^ d))))
    (fun t => earliestTime d t.val + 2 ^ (d + 1) ≤ D)
  have split' : (eligiblePrefixes d D).card +
      (Finset.univ.filter (fun t : Fin (2 ^ d) => ¬ earliestTime d t.val + 2 ^ (d + 1) ≤ D)).card =
      2 ^ d := by simpa [eligiblePrefixes] using split
  have power : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; omega
  have small : d + 1 ≤ 2 ^ (d + 1) := (Nat.lt_two_pow_self).le
  refine ⟨support, ?_, ?_⟩
  · rw [singleShape]
    change (Finset.univ.filter (fun t : Fin (2 ^ d) => ¬ earliestTime d t.val + 2 ^ (d + 1) ≤ D)).card = d + 1 - q.card
    omega
  · rw [actual_types_card d b D deadline]
    exact counts

end D5.S3.Observer.Budget.ActualDyadicDeadlineSupport
