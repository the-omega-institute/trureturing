/- GID: D5/S3/ConceptDynamics/Coding/ActualDyadicCausalPrefixRepairCapacity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ActualDyadicCausalPrefixRepairCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual dyadic continuations force midpoint traces and pair-local final queries. -/

import D5.S3.ConceptDynamics.Coding.ActualDyadicAcquisitionTrace
import D5.S3.ConceptDynamics.Coding.ClosedPhaseBallOverlap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.ActualDyadicCausalPrefixRepairCapacity

/-- A finite physical prefix ending at an acquired complete record. There is no
successful-stop or fuel-cutoff constructor in this prefix relation. -/
inductive ReachedRecord {P : Nat} (positive : 0 < P) (b : Fin 2)
    (policy : Record → Action P) (r : Fin P) : Record → Record → Prop where
  | here (record : Record) : ReachedRecord positive b policy r record record
  | advanced {start finish : Record} (choice : policy start = .advance)
      (rest : ReachedRecord positive b policy r
        { start with events := start.events + 1 } finish) :
      ReachedRecord positive b policy r start finish
  | queried {start finish : Record} (choice : policy start = .read)
      (rest : ReachedRecord positive b policy r
        { start with reads := start.reads ++
          [(start.events, rawSensor positive b r start.events)] } finish) :
      ReachedRecord positive b policy r start finish

/-- Normalize the actually acquired raw bits and fold them in chronological order.
In characteristic two, adding the known offset is its modular subtraction. -/
def acquiredPrefix {P : Nat} (b : Fin 2) : List (Nat × Fin 2) → Nat → Nat
  | [], v => v
  | (N, bit) :: tail, v =>
      acquiredPrefix (P := P) b tail (2 * v + (bit.val + b.val + N / P) % 2)

/-- The all-source successful dyadic schedule supplies a reached pre-final record.
Its chronological normalized fold is the source quotient by two, before the last
raw bit is read. Both members of each source pair reach the same final query. -/
theorem actual_acquired_prefix_and_final_query
    {P : Nat} (positive : 0 < P) (d : Nat) (power : P = 2 ^ (d + 1))
    (b : Fin 2) (policy : Record → Action P)
    (success : ∀ r : Fin P, ∃ word terminal,
      Execution positive b policy r ⟨0, []⟩ word terminal ∧
        word.length ≤ d + 1 ∧ terminal.2 = r)
    (r s : Fin P) (samePair : r.val / 2 = s.val / 2)
    (word word' : List (Fin 2)) (terminal terminal' : Record × Fin P)
    (execution : Execution positive b policy r ⟨0, []⟩ word terminal)
    (execution' : Execution positive b policy s ⟨0, []⟩ word' terminal')
    (bounded : word.length ≤ d + 1) (bounded' : word'.length ≤ d + 1) :
    ∃ past N bit bit', word.length = d + 1 ∧ word'.length = d + 1 ∧
      past.length = d ∧ acquiredPrefix (P := P) b past 0 = r.val / 2 ∧
      terminal.1.reads = past ++ [(N, bit)] ∧
      terminal'.1.reads = past ++ [(N, bit')] ∧
      ReachedRecord positive b policy r ⟨0, []⟩ ⟨N, past⟩ ∧
      ReachedRecord positive b policy s ⟨0, []⟩ ⟨N, past⟩ ∧
      N % P = P - 1 - 2 * (r.val / 2) ∧
      bit.val = (b.val + N / P + r.val % 2) % 2 ∧
      bit'.val = (b.val + N / P + s.val % 2) % 2 ∧
      policy ⟨N, past⟩ = .read ∧
      Execution positive b policy r ⟨N, past ++ [(N, bit)]⟩ [] terminal ∧
      Execution positive b policy s ⟨N, past ++ [(N, bit')]⟩ [] terminal' := by
  classical
  have splitLast : ∀ (source : Fin P) (start : Record) (bits : List (Fin 2))
      (finish : Record × Fin P),
      Execution positive b policy source start bits finish → bits ≠ [] →
      ∃ past N bit, finish.1.reads = start.reads ++ (past ++ [(N, bit)]) ∧
        past.length + 1 = bits.length ∧
        ReachedRecord positive b policy source start ⟨N, start.reads ++ past⟩ := by
    have emptyReads : ∀ (source : Fin P) (start : Record) (finish : Record × Fin P),
        Execution positive b policy source start [] finish → finish.1.reads = start.reads := by
      intro source start finish run
      generalize he : ([] : List (Fin 2)) = bits at run
      induction run with
      | stopped choice => rfl
      | advanced choice rest ih => exact ih he
      | queried choice rest ih => cases he
    intro source start bits finish run
    induction run with
    | stopped choice => intro h; exact False.elim (h rfl)
    | @advanced start bits finish choice rest ih =>
        intro h
        obtain ⟨past, N, bit, reads, length, reached⟩ := ih h
        exact ⟨past, N, bit, reads, length, .advanced choice reached⟩
    | @queried start bits finish choice rest ih =>
        intro _
        by_cases empty : bits = []
        · subst bits
          refine ⟨[], start.events, rawSensor positive b source start.events,
            ?_, by simp, ?_⟩
          · simpa using emptyReads source _ finish rest
          · simpa using (ReachedRecord.here (positive := positive) (b := b)
              (policy := policy) (r := source) start)
        · obtain ⟨past, N, bit, reads, length, reached⟩ := ih empty
          refine ⟨(start.events, rawSensor positive b source start.events) :: past,
            N, bit, ?_, by simpa using length, ?_⟩
          · simpa [List.append_assoc] using reads
          · simpa [List.append_assoc] using ReachedRecord.queried choice reached
  have traceFold : ∀ (a k : Nat) (trace : List (Nat × Fin 2)) (v : Nat),
      a ≤ r.val → r.val < a + 2 ^ k → ForcedReadTrace b r a k trace →
      trace.length = k ∧ acquiredPrefix (P := P) b trace v = v * 2 ^ k + (r.val - a) := by
    intro a k
    induction k generalizing a with
    | zero =>
        intro trace v lower upper forced
        change trace = [] at forced
        subst trace
        have eq : r.val = a := by simp only [pow_zero] at upper; omega
        simp [acquiredPrefix, eq]
    | succ k ih =>
        intro trace v lower upper forced
        obtain ⟨N, bit, tail, rfl, phase, value, forcedTail⟩ := forced
        have hp : 0 < 2 ^ k := by positivity
        have step : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by simp [pow_succ]; omega
        by_cases low : r.val < a + 2 ^ k
        · have normalized : (bit.val + b.val + N / P) % 2 = 0 := by
            simp only [if_pos low] at value
            omega
          simp only [if_pos low, zero_mul, add_zero] at forcedTail
          obtain ⟨len, fold⟩ := ih a tail (2 * v) lower low forcedTail
          refine ⟨by simp [len], ?_⟩
          simp only [acquiredPrefix, normalized, add_zero]
          rw [fold, pow_succ]
          ring
        · have normalized : (bit.val + b.val + N / P) % 2 = 1 := by
            simp only [if_neg low] at value
            omega
          simp only [if_neg low, one_mul] at forcedTail
          obtain ⟨len, fold⟩ := ih (a + 2 ^ k) tail (2 * v + 1)
            (by omega) (by rw [step] at upper; omega) forcedTail
          refine ⟨by simp [len], ?_⟩
          simp only [acquiredPrefix, normalized]
          rw [fold, pow_succ]
          have sub : r.val - a = 2 ^ k + (r.val - (a + 2 ^ k)) := by omega
          rw [sub]
          ring
  have foldAppend : ∀ (xs ys : List (Nat × Fin 2)) (v : Nat),
      acquiredPrefix (P := P) b (xs ++ ys) v =
        acquiredPrefix (P := P) b ys (acquiredPrefix (P := P) b xs v) := by
    intro xs
    induction xs with
    | nil => intro ys v; rfl
    | cons item xs ih => intro ys v; cases item; simpa [acquiredPrefix] using ih ys _
  have capacity := actual_continuation_capacity_and_saturation positive b policy
    ⟨0, []⟩ (d + 1) Finset.univ (by intro source _; exact success source)
  have card : (Finset.univ : Finset (Fin P)).card = 2 ^ (d + 1) := by simp [power]
  have length := capacity.2 card r (Finset.mem_univ r) word terminal execution bounded
  have length' := capacity.2 card s (Finset.mem_univ s) word' terminal' execution' bounded'
  have intervalSuccess : ∀ source : Fin P, 0 ≤ source.val →
      source.val < 0 + 2 ^ (d + 1) → ∃ bits finish,
      Execution positive b policy source ⟨0, []⟩ bits finish ∧
        bits.length ≤ d + 1 ∧ finish.2 = source := by
    intro source _ _; exact success source
  have within : 0 + 2 ^ (d + 1) ≤ P := by omega
  have upper : r.val < 0 + 2 ^ (d + 1) := by have h := r.isLt; omega
  have upper' : s.val < 0 + 2 ^ (d + 1) := by have h := s.isLt; omega
  obtain ⟨trace, reads, forced⟩ := actual_dyadic_interval_trace positive b policy
    ⟨0, []⟩ 0 (d + 1) within intervalSuccess r (Nat.zero_le _) upper
      word terminal execution bounded
  obtain ⟨trace', reads', forced'⟩ := actual_dyadic_interval_trace positive b policy
    ⟨0, []⟩ 0 (d + 1) within intervalSuccess s (Nat.zero_le _) upper'
      word' terminal' execution' bounded'
  obtain ⟨past, N, bit, bit', shape, shape', phase, value, value', choice, rest, rest'⟩ :=
    actual_pair_common_final_query positive b policy ⟨0, []⟩ 0 d (by exact ⟨0, rfl⟩)
      within r s samePair (Nat.zero_le _) upper (Nat.zero_le _) upper'
      word word' terminal terminal' execution execution' length length'
      trace trace' reads reads' forced forced'
  obtain ⟨traceLength, fullFold⟩ := traceFold 0 (d + 1) trace 0 (Nat.zero_le _) upper forced
  rw [shape] at traceLength fullFold
  have pastLength : past.length = d := by simp only [List.length_append,
    List.length_singleton] at traceLength; omega
  have normalized : (bit.val + b.val + N / P) % 2 = r.val % 2 := by
    have modlt := Nat.mod_lt r.val (by decide : 0 < 2)
    omega
  have decoded : acquiredPrefix (P := P) b past 0 = r.val / 2 := by
    rw [foldAppend] at fullFold
    simp only [acquiredPrefix, normalized, zero_mul, zero_add, Nat.sub_zero] at fullFold
    omega
  have reach (source : Fin P) (bits : List (Fin 2)) (finish : Record × Fin P)
      (run : Execution positive b policy source ⟨0, []⟩ bits finish)
      (len : bits.length = d + 1) (lastBit : Fin 2)
      (eqReads : finish.1.reads = past ++ [(N, lastBit)]) :
      ReachedRecord positive b policy source ⟨0, []⟩ ⟨N, past⟩ := by
    obtain ⟨past', M, lastBit', sameReads, len', reached⟩ := splitLast source
      ⟨0, []⟩ bits finish run (by intro h; simp [h] at len)
    simp only [List.nil_append] at sameReads reached
    have eqLists : past' ++ [(M, lastBit')] = past ++ [(N, lastBit)] :=
      sameReads.symm.trans eqReads
    have lenPast : past'.length = past.length := by omega
    obtain ⟨samePast, sameLast⟩ := List.append_inj eqLists lenPast
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at sameLast
    rcases sameLast with ⟨rfl, rfl⟩
    simpa [samePast] using reached
  simp only [List.nil_append] at reads reads' choice rest rest'
  rw [shape] at reads
  rw [shape'] at reads'
  exact ⟨past, N, bit, bit', length, length', pastLength, decoded, reads, reads',
    reach r word terminal execution length bit reads,
    reach s word' terminal' execution' length' bit' reads', phase, value, value',
    choice, rest, rest'⟩


/-- The actual pair-local last-query phase, represented on the real circle. -/
def terminalPhase {P : Nat} (r : Fin P) : AddCircle (P : ℝ) :=
  (((P - 1 - 2 * (r.val / 2) : Nat) : ℝ) : AddCircle (P : ℝ))

/-- The integer circular distance between the acquired source prefixes. -/
def prefixCircularDistance {P : Nat} (r s : Fin P) : Nat :=
  min (Nat.dist (r.val / 2) (s.val / 2))
    (P / 2 - Nat.dist (r.val / 2) (s.val / 2))

/-- An operational alphabet is feasible when one prefix label and one receiver
recover every actual source under every admissible closed circular error. -/
def OperationalRepairFeasible {P : Nat} (positive : 0 < P) (b : Fin 2)
    (query : Fin P → Nat) (ε : ℝ) (K : Nat) : Prop :=
  ∃ z : Nat → Fin K, ∃ decoder : AddCircle (P : ℝ) → Fin 2 → Fin K → Fin P,
    ∀ (r : Fin P) (q : AddCircle (P : ℝ)), dist q (terminalPhase r) ≤ ε →
      decoder q (rawSensor positive b r (query r)) (z (r.val / 2)) = r

/-- The least feasible operational alphabet size. Its existence and causal
realization are proved from actual success, before any coloring interpretation. -/
noncomputable def operationalLabelMinimum {P : Nat} (positive : 0 < P) (b : Fin 2)
    (query : Fin P → Nat) (ε : ℝ) : Nat :=
  sInf {K | OperationalRepairFeasible positive b query ε K}

/-- Actual all-source executions supply a causal writer and a uniform all-error
receiver exactly when its prefix labels separate overlapping closed phase balls.
The decoder selects a prefix from the phase and label alone, then subtracts the
known initial bit and the replayed event quotient in `ZMod 2`. -/
theorem actual_causal_closed_error_recovery
    {P : Nat} (positive : 0 < P) (d : Nat) (power : P = 2 ^ (d + 1))
    (b : Fin 2) (policy : Record → Action P)
    (success : ∀ r : Fin P, ∃ word terminal,
      Execution positive b policy r ⟨0, []⟩ word terminal ∧
        word.length ≤ d + 1 ∧ terminal.2 = r) :
    ∃ (history : Fin P → List (Nat × Fin 2)) (query : Fin P → Nat),
      (∀ r : Fin P, ∃ word terminal,
        Execution positive b policy r ⟨0, []⟩ word terminal ∧
        word.length = d + 1 ∧ terminal.2 = r ∧
        (history r).length = d ∧
        acquiredPrefix (P := P) b (history r) 0 = r.val / 2 ∧
        ReachedRecord positive b policy r ⟨0, []⟩ ⟨query r, history r⟩ ∧
        terminal.1.reads = history r ++ [(query r, rawSensor positive b r (query r))] ∧
        query r % P = P - 1 - 2 * (r.val / 2)) ∧
      (∀ r s : Fin P, r.val / 2 = s.val / 2 →
        history r = history s ∧ query r = query s) ∧
      (∀ r s : Fin P, history r = history s ↔ r.val / 2 = s.val / 2) ∧
      (∀ r s : Fin P, dist (terminalPhase r) (terminalPhase s) =
        2 * (prefixCircularDistance r s : ℝ)) ∧
      (∀ (r : Fin P) (word : List (Fin 2)) (terminal : Record × Fin P),
        Execution positive b policy r ⟨0, []⟩ word terminal → word.length ≤ d + 1 →
        terminal.1.reads = history r ++ [(query r, rawSensor positive b r (query r))]) ∧
      ∀ (ε : ℝ), 0 ≤ ε →
        IsLeast {K | OperationalRepairFeasible positive b query ε K}
          (operationalLabelMinimum positive b query ε) ∧
        ∀ (K : Nat) (z : Nat → Fin K),
        ∃ writer : Record → Fin K,
          (∀ r : Fin P, writer ⟨query r, history r⟩ = z (r.val / 2)) ∧
          ((∃ decoder : AddCircle (P : ℝ) → Fin 2 → Fin K → Fin P,
            ∀ (r : Fin P) (q : AddCircle (P : ℝ)), dist q (terminalPhase r) ≤ ε →
              decoder q (rawSensor positive b r (query r)) (z (r.val / 2)) = r) ↔
           ∀ r s : Fin P, r.val / 2 ≠ s.val / 2 →
             dist (terminalPhase r) (terminalPhase s) ≤ 2 * ε →
             z (r.val / 2) ≠ z (s.val / 2)) := by
  classical
  have evenP : P = 2 * 2 ^ d := by rw [power, pow_succ]; omega
  have sensor (r : Fin P) (N : Nat) (phase : N % P = P - 1 - 2 * (r.val / 2)) :
      (rawSensor positive b r N).val = (b.val + N / P + r.val % 2) % 2 := by
    change ((b.val * P + r.val + N) % (2 * P)) / P = _
    rw [Nat.mod_mul_left_div_self]
    have hm := Nat.mod_add_div r.val 2
    have hn := Nat.mod_add_div N P
    have hN := Nat.mod_lt N positive
    have hr := r.isLt
    have hu := Nat.mod_lt r.val (by decide : 0 < 2)
    have rearrange : b.val * P + r.val + N =
        (r.val + N % P) + P * (b.val + N / P) := by nlinarith
    rw [rearrange, Nat.add_mul_div_left _ _ positive]
    have quotient : (r.val + N % P) / P = r.val % 2 := by
      by_cases zero : r.val % 2 = 0
      · rw [zero]
        exact Nat.div_eq_of_lt (by omega)
      · have one : r.val % 2 = 1 := by omega
        rw [one]
        exact Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [quotient]
    congr 1
    omega
  let word (r : Fin P) := (success r).choose
  let terminal (r : Fin P) := (success r).choose_spec.choose
  have run (r : Fin P) : Execution positive b policy r ⟨0, []⟩ (word r) (terminal r) ∧
      (word r).length ≤ d + 1 ∧ (terminal r).2 = r :=
    (success r).choose_spec.choose_spec
  have info (r : Fin P) : ∃ past N,
      past.length = d ∧ acquiredPrefix (P := P) b past 0 = r.val / 2 ∧
      ReachedRecord positive b policy r ⟨0, []⟩ ⟨N, past⟩ ∧
      (terminal r).1.reads = past ++ [(N, rawSensor positive b r N)] ∧
      N % P = P - 1 - 2 * (r.val / 2) ∧ (word r).length = d + 1 := by
    obtain ⟨past, N, bit, bit', len, len', pastLen, decoded, reads, reads',
      reached, reached', phase, value, value', choice, rest, rest'⟩ :=
      actual_acquired_prefix_and_final_query positive d power b policy success r r rfl
        (word r) (word r) (terminal r) (terminal r) (run r).1 (run r).1
        (run r).2.1 (run r).2.1
    have eqBit : bit = rawSensor positive b r N := by
      apply Fin.ext
      exact value.trans (sensor r N phase).symm
    exact ⟨past, N, pastLen, decoded, reached, by simpa [eqBit] using reads, phase, len⟩
  choose history query data using info
  have lastUnique (xs ys : List (Nat × Fin 2)) (N M : Nat) (a c : Fin 2)
      (len : xs.length = ys.length) (eq : xs ++ [(N, a)] = ys ++ [(M, c)]) :
      xs = ys ∧ N = M := by
    obtain ⟨samePast, sameLast⟩ := List.append_inj eq len
    simp only [List.cons.injEq, Prod.mk.injEq, and_true] at sameLast
    exact ⟨samePast, sameLast.1⟩
  have pairData (r s : Fin P) (pair : r.val / 2 = s.val / 2) :
      history r = history s ∧ query r = query s := by
    obtain ⟨past, N, bit, bit', len, len', pastLen, decoded, reads, reads',
      reached, reached', phase, value, value', choice, rest, rest'⟩ :=
      actual_acquired_prefix_and_final_query positive d power b policy success r s pair
        (word r) (word s) (terminal r) (terminal s) (run r).1 (run s).1
        (run r).2.1 (run s).2.1
    have left := lastUnique (history r) past (query r) N _ _
      ((data r).1.trans pastLen.symm) ((data r).2.2.2.1.symm.trans reads)
    have right := lastUnique (history s) past (query s) N _ _
      ((data s).1.trans pastLen.symm) ((data s).2.2.2.1.symm.trans reads')
    exact ⟨left.1.trans right.1.symm, left.2.trans right.2.symm⟩
  have actualReads (r : Fin P) (bits : List (Fin 2)) (finish : Record × Fin P)
      (execution : Execution positive b policy r ⟨0, []⟩ bits finish)
      (bounded : bits.length ≤ d + 1) :
      finish.1.reads = history r ++ [(query r, rawSensor positive b r (query r))] := by
    obtain ⟨past, N, bit, bit', len, len', pastLen, decoded, reads, reads',
      reached, reached', phase, value, value', choice, rest, rest'⟩ :=
      actual_acquired_prefix_and_final_query positive d power b policy success r r rfl
        (word r) bits (terminal r) finish (run r).1 execution (run r).2.1 bounded
    have same := lastUnique (history r) past (query r) N _ _
      ((data r).1.trans pastLen.symm) ((data r).2.2.2.1.symm.trans reads)
    have eqBit : bit' = rawSensor positive b r N := by
      apply Fin.ext
      exact value'.trans (sensor r N phase).symm
    simpa [← same.1, ← same.2, eqBit] using reads'
  have historyIff (r s : Fin P) : history r = history s ↔ r.val / 2 = s.val / 2 := by
    constructor
    · intro same
      have fold := congrArg (fun past => acquiredPrefix (P := P) b past 0) same
      simpa only [(data r).2.1, (data s).2.1] using fold
    · intro same
      exact (pairData r s same).1
  have phaseDistance : ∀ r s : Fin P, dist (terminalPhase r) (terminalPhase s) =
      2 * (prefixCircularDistance r s : ℝ) := by
    have ordered (r s : Fin P) (order : r.val / 2 ≤ s.val / 2) :
        dist (terminalPhase r) (terminalPhase s) =
          2 * (prefixCircularDistance r s : ℝ) := by
      let delta := s.val / 2 - r.val / 2
      let n := P / 2
      have half : n = 2 ^ d := by dsimp [n]; omega
      have np : 0 < n := by rw [half]; positivity
      have rlt : r.val / 2 < n := by have h := r.isLt; dsimp [n]; omega
      have slt : s.val / 2 < n := by have h := s.isLt; dsimp [n]; omega
      have deltaLt : delta < n := by dsimp [delta]; omega
      have Pn : (P : ℝ) = 2 * (n : ℝ) := by
        exact_mod_cast (show P = 2 * n by dsimp [n]; omega)
      have hp : (P : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
      have rsub : 2 * (r.val / 2) ≤ P - 1 := by have h := r.isLt; omega
      have ssub : 2 * (s.val / 2) ≤ P - 1 := by have h := s.isLt; omega
      have difference : ((P - 1 - 2 * (r.val / 2) : Nat) : ℝ) -
          ((P - 1 - 2 * (s.val / 2) : Nat) : ℝ) = 2 * (delta : ℝ) := by
        dsimp [delta]
        rw [Nat.cast_sub rsub, Nat.cast_sub ssub, Nat.cast_sub order]
        push_cast
        ring
      rw [dist_eq_norm]
      unfold terminalPhase
      rw [← AddCircle.coe_sub, difference]
      have cd : prefixCircularDistance r s = min delta (n - delta) := by
        simp only [prefixCircularDistance, Nat.dist_eq_sub_of_le order]
        rfl
      rw [cd]
      by_cases small : delta ≤ n - delta
      · rw [min_eq_left small]
        have bound : |2 * (delta : ℝ)| ≤ |(P : ℝ)| / 2 := by
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), Pn]
          have h : 2 * (delta : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (show 2 * delta ≤ n by omega)
          linarith
        rw [(AddCircle.norm_coe_eq_abs_iff (P : ℝ) hp).2 bound,
          abs_of_nonneg (by positivity)]
      · have large : n - delta ≤ delta := by omega
        rw [min_eq_right large]
        have neg : 2 * (delta : ℝ) - (P : ℝ) ≤ 0 := by
          have h : (delta : ℝ) ≤ (n : ℝ) := by exact_mod_cast deltaLt.le
          linarith
        have bound : |2 * (delta : ℝ) - (P : ℝ)| ≤ |(P : ℝ)| / 2 := by
          rw [abs_of_nonpos neg, abs_of_nonneg (by positivity), Pn]
          have h : (n : ℝ) ≤ 2 * (delta : ℝ) := by
            exact_mod_cast (show n ≤ 2 * delta by omega)
          linarith
        have shift : ((2 * (delta : ℝ) - (P : ℝ) : ℝ) : AddCircle (P : ℝ)) =
            ((2 * (delta : ℝ) : ℝ) : AddCircle (P : ℝ)) := by
          simp only [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
        rw [← shift, (AddCircle.norm_coe_eq_abs_iff (P : ℝ) hp).2 bound,
          abs_of_nonpos neg, Nat.cast_sub deltaLt.le]
        linarith
    intro r s
    rcases le_total (r.val / 2) (s.val / 2) with order | order
    · exact ordered r s order
    · rw [dist_comm]
      have same : prefixCircularDistance s r = prefixCircularDistance r s := by
        simp only [prefixCircularDistance, Nat.dist_comm]
      simpa only [same] using ordered s r order
  refine ⟨history, query, ?_, pairData, historyIff, phaseDistance, actualReads, ?_⟩
  · intro r
    exact ⟨word r, terminal r, (run r).1, (data r).2.2.2.2.2, (run r).2.2,
      (data r).1, (data r).2.1, (data r).2.2.1, (data r).2.2.2.1,
      (data r).2.2.2.2.1⟩
  intro ε nonneg
  have characterize :
      ∀ (K : Nat) (z : Nat → Fin K),
      ∃ writer : Record → Fin K,
        (∀ r : Fin P, writer ⟨query r, history r⟩ = z (r.val / 2)) ∧
        ((∃ decoder : AddCircle (P : ℝ) → Fin 2 → Fin K → Fin P,
          ∀ (r : Fin P) (q : AddCircle (P : ℝ)), dist q (terminalPhase r) ≤ ε →
            decoder q (rawSensor positive b r (query r)) (z (r.val / 2)) = r) ↔
         ∀ r s : Fin P, r.val / 2 ≠ s.val / 2 →
           dist (terminalPhase r) (terminalPhase s) ≤ 2 * ε →
           z (r.val / 2) ≠ z (s.val / 2)) := by
    intro K z
    let writer : Record → Fin K := fun record => z (acquiredPrefix (P := P) b record.reads 0)
    refine ⟨writer, (by intro r; exact congrArg z (data r).2.1), ?_⟩
    have overlap :=
      D5.S3.ConceptDynamics.Coding.ClosedPhaseBallOverlap.closed_phase_ball_overlap P ε
    have rawCast (r : Fin P) :
        ((rawSensor positive b r (query r)).val : ZMod 2) =
          (b.val : ZMod 2) + ((query r / P : Nat) : ZMod 2) + ((r.val % 2 : Nat) : ZMod 2) := by
      rw [sensor r (query r) (data r).2.2.2.2.1]
      simp only [Nat.cast_add, ZMod.natCast_mod]
    have sourceBound (r : Fin P) (u : Nat) (small : u < 2) :
        2 * (r.val / 2) + u < P := by
      have hr := r.isLt
      omega
    constructor
    · rintro ⟨decoder, correct⟩ r s distinct close sameLabel
      obtain ⟨q, qr, qs⟩ := (overlap (terminalPhase r) (terminalPhase s)).2 close
      let ur : ZMod 2 := -(b.val : ZMod 2) - ((query r / P : Nat) : ZMod 2)
      let us : ZMod 2 := -(b.val : ZMod 2) - ((query s / P : Nat) : ZMod 2)
      let r0 : Fin P := ⟨2 * (r.val / 2) + ur.val, sourceBound r ur.val ur.val_lt⟩
      let s0 : Fin P := ⟨2 * (s.val / 2) + us.val, sourceBound s us.val us.val_lt⟩
      have rp : r0.val / 2 = r.val / 2 := by dsimp [r0]; have h := ur.val_lt; omega
      have sp : s0.val / 2 = s.val / 2 := by dsimp [s0]; have h := us.val_lt; omega
      have rz : rawSensor positive b r0 (query r0) = 0 := by
        have cast := rawCast r0
        rw [(pairData r0 r rp).2] at cast
        have mod : r0.val % 2 = ur.val := by dsimp [r0]; have h := ur.val_lt; omega
        rw [mod, ZMod.natCast_zmod_val] at cast
        have eqZero : ((rawSensor positive b r0 (query r0)).val : ZMod 2) = 0 := by
          rw [(pairData r0 r rp).2, cast]; dsimp [ur]; ring
        apply Fin.ext
        have value := congrArg ZMod.val eqZero
        simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (rawSensor positive b r0 (query r0)).isLt] using value
      have sz : rawSensor positive b s0 (query s0) = 0 := by
        have cast := rawCast s0
        rw [(pairData s0 s sp).2] at cast
        have mod : s0.val % 2 = us.val := by dsimp [s0]; have h := us.val_lt; omega
        rw [mod, ZMod.natCast_zmod_val] at cast
        have eqZero : ((rawSensor positive b s0 (query s0)).val : ZMod 2) = 0 := by
          rw [(pairData s0 s sp).2, cast]; dsimp [us]; ring
        apply Fin.ext
        have value := congrArg ZMod.val eqZero
        simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (rawSensor positive b s0 (query s0)).isLt] using value
      have cr := correct r0 q (by simpa [terminalPhase, rp] using qr)
      have cs := correct s0 q (by simpa [terminalPhase, sp] using qs)
      rw [rz, rp] at cr
      rw [sz, sp, ← sameLabel] at cs
      have sameSource : r0 = s0 := cr.symm.trans cs
      exact distinct (rp.symm.trans ((congrArg (fun v : Fin P => v.val / 2) sameSource).trans sp))
    · intro separated
      let candidates (q : AddCircle (P : ℝ)) (label : Fin K) : Prop :=
        ∃ r : Fin P, dist q (terminalPhase r) ≤ ε ∧ z (r.val / 2) = label
      let decoder : AddCircle (P : ℝ) → Fin 2 → Fin K → Fin P := fun q Y label =>
        if actual : candidates q label then
          let r := actual.choose
          let u : ZMod 2 := (Y.val : ZMod 2) - (b.val : ZMod 2) - ((query r / P : Nat) : ZMod 2)
          ⟨2 * (r.val / 2) + u.val, sourceBound r u.val u.val_lt⟩
        else ⟨0, positive⟩
      refine ⟨decoder, ?_⟩
      intro r q admissible
      have actual : candidates q (z (r.val / 2)) := ⟨r, admissible, rfl⟩
      let chosen : Fin P := actual.choose
      have chosenNoise : dist q (terminalPhase chosen) ≤ ε := actual.choose_spec.1
      have chosenLabel : z (chosen.val / 2) = z (r.val / 2) := actual.choose_spec.2
      have samePrefix : chosen.val / 2 = r.val / 2 := by
        by_contra different
        have close : dist (terminalPhase chosen) (terminalPhase r) ≤ 2 * ε :=
          (overlap _ _).1 ⟨q, chosenNoise, admissible⟩
        exact separated chosen r different close chosenLabel
      have sameQuery := (pairData chosen r samePrefix).2
      have invert : ((rawSensor positive b r (query r)).val : ZMod 2) -
          (b.val : ZMod 2) - ((query chosen / P : Nat) : ZMod 2) = ((r.val % 2 : Nat) : ZMod 2) := by
        rw [sameQuery, rawCast]
        ring
      have invertVal : (((rawSensor positive b r (query r)).val : ZMod 2) -
          (b.val : ZMod 2) - ((query chosen / P : Nat) : ZMod 2)).val = r.val % 2 := by
        rw [invert, ZMod.val_natCast]
        exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
      dsimp only [decoder]
      rw [dif_pos actual]
      apply Fin.ext
      change 2 * (chosen.val / 2) + _ = r.val
      rw [invertVal, samePrefix]
      have h := Nat.mod_add_div r.val 2
      omega
  let zFull : Nat → Fin (2 ^ d) := fun t => ⟨t % 2 ^ d, Nat.mod_lt _ (by positivity)⟩
  obtain ⟨writer, causal, equivalence⟩ := characterize (2 ^ d) zFull
  have separated : ∀ r s : Fin P, r.val / 2 ≠ s.val / 2 →
      dist (terminalPhase r) (terminalPhase s) ≤ 2 * ε →
      zFull (r.val / 2) ≠ zFull (s.val / 2) := by
    intro r s different _ same
    have hr : r.val / 2 < 2 ^ d := by have h := r.isLt; omega
    have hs : s.val / 2 < 2 ^ d := by have h := s.isLt; omega
    have values := congrArg Fin.val same
    simp only [zFull, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at values
    exact different values
  obtain ⟨decoder, correct⟩ := equivalence.2 separated
  have nonempty : {K | OperationalRepairFeasible positive b query ε K}.Nonempty :=
    ⟨2 ^ d, zFull, decoder, correct⟩
  exact ⟨⟨Nat.sInf_mem nonempty, fun K member => Nat.sInf_le member⟩, characterize⟩

#print axioms actual_causal_closed_error_recovery

#print axioms actual_acquired_prefix_and_final_query

#print axioms actual_pair_common_final_query
#print axioms actual_dyadic_interval_trace
#print axioms actual_continuation_capacity_and_saturation
#print axioms actual_next_read_decomposition

end D5.S3.ConceptDynamics.Coding.ActualDyadicCausalPrefixRepairCapacity
