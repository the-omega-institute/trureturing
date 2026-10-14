/- GID: D5/S3/Estimation/SequentialDecisionRisk/NativeBernsteinStageMass
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/NativeBernsteinStageMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous actual Bernstein batch masses for a single source table. -/

import D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinScheduledExecution

noncomputable section
open scoped BigOperators ENNReal

namespace D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinStageMass
open NativeBernsteinScheduledExecution NativeBernsteinBatchExecution
  SeededBernoulliFactoryExecution MeasureTheory ProbabilityTheory

private theorem success_le_source (h : History) (s : Bool) :
    successCount s h ≤ sourceCount s h := by
  have hb := List.length_filter_le (fun v : Bool × Bool => decide (v.2 = true))
    (h.filter (fun v => decide (v.1 = s)))
  simpa [successCount, sourceCount, List.filter_filter, Bool.and_comm] using hb

private theorem sum_fin_cut (f : ℕ → ℝ≥0∞) (n N : ℕ) (hn : n ≤ N)
    (hz : ∀ i, n < i → i ≤ N → f i = 0) :
    (∑ i : Fin (N+1), f i.val) = ∑ i : Fin (n+1), f i.val := by
  rw [Fin.sum_univ_eq_sum_range f (N+1), Fin.sum_univ_eq_sum_range f (n+1)]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
  intro i hi hn'
  have hh : ¬ i < n+1 := by simpa only [Finset.mem_range] using hn'
  exact hz i (by omega) (by have := Finset.mem_range.mp hi; omega)

section StageMass
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)
local notation "μ" => rawLaw (rowLaw (batchTable D d a hD hd hc))

def arrivalMass (S : Bool) (p q : unitInterval) (k I J : ℕ) : ℝ≥0∞ :=
  μ {ω | ((D k+d k : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
    countPair (nativeHistory π S p q (D k+d k) ω) = (I,J)}

def unresolvedMass (S : Bool) (p q : unitInterval) (k I J : ℕ) : ℝ≥0∞ :=
  μ {ω | ((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω ∧
    countPair (nativeHistory π S p q (D k+d k) ω) = (I,J)}

def actionMass (S : Bool) (p q : unitInterval) (k I J : ℕ) (r : Option Bool) : ℝ≥0∞ :=
  μ {ω | ((D k+d k : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
    countPair (nativeHistory π S p q (D k+d k) ω) = (I,J) ∧
    nativeAction π S p q (D k+d k) ω = encodeStage σ (D k+d k) r}

private theorem unresolved_is_call (S : Bool) (p q : unitInterval) (k I J : ℕ) :
    unresolvedMass D d a hD hd hc S p q k I J =
      actionMass D d a hD hd hc S p q k I J none := by
  apply congrArg μ
  ext ω
  constructor
  · rintro ⟨ht,hij⟩
    obtain ⟨s,hs⟩ := call_before_return π S (sourceRead p q) ω (D k+d k) ht
    have hl := acquired_history_length_before_return π S (sourceRead p q) ω (D k+d k) ht.le
    have hh := (safe_supported_actions D d a hD hd hc ω.1 S
      (nativeHistory π S p q (D k+d k) ω)).1 s hs
    change (nativeHistory π S p q (D k+d k) ω).length = D k+d k at hl
    rw [hl] at hh
    change nativeAction π S p q (D k+d k) ω = .inl s at hs
    exact ⟨ht.le,hij,by simpa only [encodeStage, hh] using hs⟩
  · rintro ⟨ht,hij,ha⟩
    have hl := acquired_history_length_before_return π S (sourceRead p q) ω (D k+d k) ht
    have hh := native_history_call_step π S p q (D k+d k) ω (σ (D k+d k)) ha
    have hn : (nativeHistory π S p q (D k+d k+1) ω).length = D k+d k+1 := by
      rw [hh, List.length_append, List.length_singleton]
      exact congrArg (· + 1) hl
    exact ⟨(WithTop.coe_lt_coe.mpr (Nat.lt_succ_self _)).trans_le
      ((native_full_history_iff π S p q _ ω).mp hn),hij⟩

private theorem unresolved_outside (S : Bool) (p q : unitInterval) (k I J : ℕ)
    (hij : D k < I ∨ d k < J) : unresolvedMass D d a hD hd hc S p q k I J = 0 := by
  apply measure_mono_null (t := ∅) _ measure_empty
  intro ω hω
  have hsrc := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.1 k hω.1.le
  have hi := success_le_source (nativeHistory π S p q (D k+d k) ω) false
  have hj := success_le_source (nativeHistory π S p q (D k+d k) ω) true
  rw [hsrc.1] at hi
  rw [hsrc.2] at hj
  have hei := congrArg Prod.fst hω.2
  have hej := congrArg Prod.snd hω.2
  simp only [countPair] at hei hej
  rcases hij with hij | hij <;> omega

/-- One fixed table realizes all incoming, exiting and unresolved coefficient
masses at once, on the actual native execution law and at every batch. -/
theorem one_table_all_stage_joint_mass (S : Bool) (p q : unitInterval) :
    ∀ k (i : Fin (D k+1)) (j : Fin (d k+1)),
      arrivalMass D d a hD hd hc S p q k i.val j.val =
        ENNReal.ofReal (incomingCoefficients D d a k i j) *
          binomialMass (D k) i.val p * binomialMass (d k) j.val q ∧
      unresolvedMass D d a hD hd hc S p q k i.val j.val =
        ENNReal.ofReal (residualCoefficients D d a k i j) *
          binomialMass (D k) i.val p * binomialMass (d k) j.val q ∧
      ∀ e, actionMass D d a hD hd hc S p q k i.val j.val (some e) =
        ENNReal.ofReal (exitCoefficients D d a k e i j) *
          binomialMass (D k) i.val p * binomialMass (d k) j.val q := by
  have hrows (k : ℕ) (i : Fin (D k+1)) (j : Fin (d k+1))
      (ha : arrivalMass D d a hD hd hc S p q k i.val j.val =
        ENNReal.ofReal (incomingCoefficients D d a k i j) *
          binomialMass (D k) i.val p * binomialMass (d k) j.val q) :
      unresolvedMass D d a hD hd hc S p q k i.val j.val =
        ENNReal.ofReal (residualCoefficients D d a k i j) *
          binomialMass (D k) i.val p * binomialMass (d k) j.val q ∧
      ∀ e, actionMass D d a hD hd hc S p q k i.val j.val (some e) =
        ENNReal.ofReal (exitCoefficients D d a k e i j) *
          binomialMass (D k) i.val p * binomialMass (d k) j.val q := by
    have he (r : Option Bool) : actionMass D d a hD hd hc S p q k i.val j.val r =
        (ENNReal.ofReal (incomingCoefficients D d a k i j) *
          fiberRow D d a hD.monotone hd.monotone hc k i j r) *
          binomialMass (D k) i.val p * binomialMass (d k) j.val q := by
      rw [actionMass, actual_count_fiber_classification]
      change arrivalMass D d a hD hd hc S p q k i.val j.val * _ = _
      rw [ha]
      ac_rfl
    constructor
    · rw [unresolved_is_call, he, (fiber_rows_classification D d a hD.monotone hd.monotone hc k i j).2]
    · intro e
      rw [he, (fiber_rows_classification D d a hD.monotone hd.monotone hc k i j).1 e]
  intro k
  induction k with
  | zero =>
    intro i j
    have ha : arrivalMass D d a hD hd hc S p q 0 i.val j.val =
        ENNReal.ofReal (incomingCoefficients D d a 0 i j) *
          binomialMass (D 0) i.val p * binomialMass (d 0) j.val q := by
      simpa only [arrivalMass, incomingCoefficients, ENNReal.ofReal_one, one_mul] using
        initial_actual_batch_mass D d a hD hd hc S p q i.val j.val
    exact ⟨ha,hrows 0 i j ha⟩
  | succ k ih =>
    intro I J
    have ha : arrivalMass D d a hD hd hc S p q (k+1) I.val J.val =
        ENNReal.ofReal (incomingCoefficients D d a (k+1) I J) *
          binomialMass (D (k+1)) I.val p * binomialMass (d (k+1)) J.val q := by
      rw [arrivalMass, actual_two_block_count_transport]
      let f (i j : ℕ) := unresolvedMass D d a hD hd hc S p q k i j *
        translatedBinomial (D (k+1)-D k) i I.val p *
        translatedBinomial (d (k+1)-d k) j J.val q
      change (∑ i : Fin (D k+d k+1), ∑ j : Fin (D k+d k+1), f i.val j.val) = _
      rw [sum_fin_cut (fun i => ∑ j : Fin (D k+d k+1), f i j.val) (D k) (D k+d k)
        (by omega) (by
          intro i hi _
          apply Finset.sum_eq_zero
          intro j _
          dsimp [f]
          rw [unresolved_outside D d a hD hd hc S p q k i j.val (Or.inl hi), zero_mul, zero_mul])]
      have hj (i : ℕ) : (∑ j : Fin (D k+d k+1), f i j.val) = ∑ j : Fin (d k+1), f i j.val := by
        apply sum_fin_cut _ (d k) (D k+d k) (by omega)
        intro j hj _
        dsimp [f]
        rw [unresolved_outside D d a hD hd hc S p q k i j (Or.inr hj), zero_mul, zero_mul]
      simp_rw [hj]
      dsimp only [f]
      simp_rw [fun i j => (ih i j).2.1]
      exact two_source_hypergeometric_lift (D k) (d k) (D (k+1)) (d (k+1))
        (hD.monotone (Nat.le_succ k)) (hd.monotone (Nat.le_succ k))
        (residualCoefficients D d a k)
        (fun i j => (coefficient_node_balance D d a hD.monotone hd.monotone hc k i j).1) p q I J
    exact ⟨ha,hrows (k+1) I J ha⟩

end StageMass

section SurvivalMass
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)
local notation "μ" => rawLaw (rowLaw (batchTable D d a hD hd hc))

private theorem landmark_count_partition (S : Bool) (p q : unitInterval) (k : ℕ)
    (E : Set (RowSeed × Tape)) (hE : MeasurableSet E)
    (hreach : ∀ ω ∈ E, ((D k+d k : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω) :
    μ E = ∑ i : Fin (D k+1), ∑ j : Fin (d k+1),
      μ {ω | ω ∈ E ∧ countPair (nativeHistory π S p q (D k+d k) ω) = (i.val,j.val)} := by
  classical
  let Tag := Fin (D k+1) × Fin (d k+1)
  let A (t : Tag) := {ω | ω ∈ E ∧
    countPair (nativeHistory π S p q (D k+d k) ω) = (t.1.val,t.2.val)}
  have he : E = ⋃ t : Tag, A t := by
    ext ω
    simp only [Set.mem_iUnion]
    constructor
    · intro hω
      have hs := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.1 k (hreach ω hω)
      have hi := success_le_source (nativeHistory π S p q (D k+d k) ω) false
      have hj := success_le_source (nativeHistory π S p q (D k+d k) ω) true
      rw [hs.1] at hi
      rw [hs.2] at hj
      exact ⟨(⟨successCount false (nativeHistory π S p q (D k+d k) ω), Nat.lt_succ_of_le hi⟩,
        ⟨successCount true (nativeHistory π S p q (D k+d k) ω), Nat.lt_succ_of_le hj⟩),hω,rfl⟩
    · rintro ⟨t,hω⟩
      exact hω.1
  have hdis : Pairwise (fun t u : Tag => Disjoint (A t) (A u)) := by
    intro t u htu
    apply Set.disjoint_left.mpr
    intro ω ht hu
    have he := ht.2.symm.trans hu.2
    exact htu (Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he)))
  have hm (t : Tag) : MeasurableSet (A t) := by
    let : MeasurableSpace History := ⊤
    have hh := (native_execution_measurable π
      (supported_realization σ (batchTable D d a hD hd hc)).1 S p q).1 (D k+d k)
    exact hE.inter (hh (show MeasurableSet
      {h : History | countPair h = (t.1.val,t.2.val)} from .of_discrete))
  conv_lhs => rw [he, measure_iUnion hdis hm, tsum_fintype]
  exact Fintype.sum_prod_type _

/-- The actual unresolved probability equals the Bernstein evaluation of the
residual coefficients, with both source counters from the same execution. -/
theorem actual_unresolved_mass (S : Bool) (p q : unitInterval) (k : ℕ) :
    μ {ω | ((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω} =
      bernsteinEval (D k) (d k) (residualCoefficients D d a k) p q := by
  have hm := (native_execution_measurable π
    (supported_realization σ (batchTable D d a hD hd hc)).1 S p q).2.2 (D k+d k)
  rw [landmark_count_partition D d a hD hd hc S p q k _ hm (fun _ h => h.le)]
  change (∑ i : Fin (D k+1), ∑ j : Fin (d k+1),
    unresolvedMass D d a hD hd hc S p q k i.val j.val) = _
  simp_rw [fun i j => (one_table_all_stage_joint_mass D d a hD hd hc S p q k i j).2.1]
  rfl

/-- Vanishing residual evaluations force almost-sure finite return for the
same single table and its actual source-count execution. -/
theorem actual_return_of_residual_limit (S : Bool) (p q : unitInterval)
    (hlim : Filter.Tendsto (fun k =>
      bernsteinEval (D k) (d k) (residualCoefficients D d a k) p q)
      Filter.atTop (nhds 0)) :
    μ {ω | nativeCalls π S p q ω = ⊤} = 0 := by
  have hb (k : ℕ) : μ {ω | nativeCalls π S p q ω = ⊤} ≤
      bernsteinEval (D k) (d k) (residualCoefficients D d a k) p q := by
    rw [← actual_unresolved_mass D d a hD hd hc S p q k]
    apply measure_mono
    intro ω hω
    change nativeCalls π S p q ω = ⊤ at hω
    simp [hω]
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hb) bot_le

end SurvivalMass

private theorem native_action_freezes {Seed : Type}
    (π : Seed → Bool → History → Action) (S : Bool) (p q : unitInterval)
    (ω : Seed × Tape) (n m : ℕ) (hnm : n ≤ m) (cell : Bool × Bool)
    (ha : nativeAction π S p q n ω = .inr cell) : nativeAction π S p q m ω = .inr cell := by
  have he := (acquired_history_geometry π S (sourceRead p q) ω).2.2 n cell ha (m-n)
  have he' : nativeHistory π S p q m ω = nativeHistory π S p q n ω := by
    simpa only [nativeHistory, Nat.add_sub_of_le hnm] using he
  simpa only [nativeAction, he'] using ha

private theorem native_return_le {Seed : Type}
    (π : Seed → Bool → History → Action) (S : Bool) (p q : unitInterval)
    (ω : Seed × Tape) (n : ℕ) (cell : Bool × Bool)
    (ha : nativeAction π S p q n ω = .inr cell) : nativeCalls π S p q ω ≤ (n : WithTop ℕ) :=
  hittingAfter_le_of_mem (Nat.zero_le n) ⟨cell,ha.symm⟩

section CumulativeOutputs
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)
local notation "μ" => rawLaw (rowLaw (batchTable D d a hD hd hc))

private theorem stage_exit_mass (S : Bool) (p q : unitInterval) (k : ℕ) (e : Bool) :
    μ {ω | ((D k+d k : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      nativeAction π S p q (D k+d k) ω = .inr (false,e)} =
        bernsteinEval (D k) (d k) (exitCoefficients D d a k e) p q := by
  let : MeasurableSpace History := ⊤
  have hm := native_execution_measurable π
    (supported_realization σ (batchTable D d a hD hd hc)).1 S p q
  have hE : MeasurableSet {ω | ((D k+d k : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      nativeAction π S p q (D k+d k) ω = .inr (false,e)} := by
    have hh := (hm.1 (D k+d k)) (show MeasurableSet {h : History | h.length = D k+d k} from .of_discrete)
    have ha := (hm.2.1 (D k+d k)) (action_singleton_measurable (.inr (false,e)))
    convert hh.inter ha using 1
    ext ω
    exact and_congr_left (fun _ => (native_full_history_iff π S p q (D k+d k) ω).symm)
  rw [landmark_count_partition D d a hD hd hc S p q k _ hE (fun _ h => h.1)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : μ {ω | ω ∈ {ω | ((D k+d k : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      nativeAction π S p q (D k+d k) ω = .inr (false,e)} ∧
      countPair (nativeHistory π S p q (D k+d k) ω) = (i.val,j.val)} =
      actionMass D d a hD hd hc S p q k i.val j.val (some e) := by
    apply congrArg μ
    ext ω
    change ((_ ∧ _) ∧ _) ↔ (_ ∧ _ ∧ _)
    tauto
  rw [he]
  exact (one_table_all_stage_joint_mass D d a hD hd hc S p q k i j).2.2 e

include hD hd hc in
private theorem exit_evaluation_balance (p q : unitInterval) (k : ℕ) (e : Bool) :
    bernsteinEval (D (k+1)) (d (k+1)) (exitCoefficients D d a (k+1) e) p q +
      bernsteinEval (D k) (d k) (a k e) p q =
      bernsteinEval (D (k+1)) (d (k+1)) (a (k+1) e) p q := by
  rw [← lift_preserves_bernstein_evaluation (D k) (d k) (D (k+1)) (d (k+1))
    (hD.monotone (Nat.le_succ k)) (hd.monotone (Nat.le_succ k)) (a k e) (hc.nonneg k e) p q]
  unfold bernsteinEval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  have hx := (coefficient_node_balance D d a hD.monotone hd.monotone hc (k+1) I J).2.2.1 e
  have hl : 0 ≤ liftTwo (D k) (d k) (D (k+1)) (d (k+1)) (a k e) I J := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (hc.nonneg k e i j)
      ((hypergeometric_stochastic_rows _ _ (hD.monotone (Nat.le_succ k)) I).1 i))
      ((hypergeometric_stochastic_rows _ _ (hd.monotone (Nat.le_succ k)) J).1 j)
  rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add hx hl]
  simp only [exitCoefficients, sub_add_cancel]

/-- By each batch boundary, the probability of an already returned color is
exactly its coefficient-array Bernstein evaluation for the same table. -/
theorem actual_cumulative_output_mass (S : Bool) (p q : unitInterval) (e : Bool) (k : ℕ) :
    μ {ω | nativeAction π S p q (D k+d k) ω = .inr (false,e)} =
      bernsteinEval (D k) (d k) (a k e) p q := by
  classical
  have hN : StrictMono (fun k => D k+d k) := fun x y h => Nat.add_lt_add (hD h) (hd h)
  induction k with
  | zero =>
    have he : {ω | nativeAction π S p q (D 0+d 0) ω = .inr (false,e)} =
        {ω | ((D 0+d 0 : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
          nativeAction π S p q (D 0+d 0) ω = .inr (false,e)} := by
      ext ω
      exact ⟨fun h => ⟨(actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.1,h⟩,
        fun h => h.2⟩
    rw [he, stage_exit_mass]
    rfl
  | succ k ih =>
    let E := {ω | nativeAction π S p q (D k+d k) ω = .inr (false,e)}
    let F := {ω | ((D (k+1)+d (k+1) : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω ∧
      nativeAction π S p q (D (k+1)+d (k+1)) ω = .inr (false,e)}
    have hn : D k+d k < D (k+1)+d (k+1) := hN (Nat.lt_succ_self k)
    have he : {ω | nativeAction π S p q (D (k+1)+d (k+1)) ω = .inr (false,e)} = E ∪ F := by
      ext ω
      constructor
      · intro hω
        by_cases ht : nativeCalls π S p q ω ≤ ((D k+d k : ℕ) : WithTop ℕ)
        · left
          obtain ⟨m,hm⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) ht)
          have hm := hm.symm
          have hmle : m ≤ D k+d k := by
            rw [hm] at ht
            exact WithTop.coe_le_coe.mp ht
          have hmem := hittingAfter_mem_set_of_ne_top
            (u := nativeAction π S p q) (s := Set.range (fun c : Bool × Bool => (Sum.inr c : Action)))
            (n := 0) (ω := ω) (show nativeCalls π S p q ω ≠ ⊤ by rw [hm]; simp)
          change nativeAction π S p q (nativeCalls π S p q ω).untopA ω ∈ _ at hmem
          rw [hm] at hmem
          obtain ⟨cell,hcell⟩ := hmem
          have ho := native_action_freezes π S p q ω m (D k+d k) hmle cell hcell.symm
          have hn' := native_action_freezes π S p q ω m (D (k+1)+d (k+1)) (hmle.trans hn.le) cell hcell.symm
          change nativeAction π S p q (D (k+1)+d (k+1)) ω = .inr (false,e) at hω
          exact ho.trans (hn'.symm.trans hω)
        · right
          have hlt := lt_of_not_ge ht
          have hb := (actual_between_landmarks D d a hD hd hc S p q ω k
            (D (k+1)+d (k+1)-1) (by omega) (by omega)).2.1
          have hp : D (k+1)+d (k+1)-1+1 = D (k+1)+d (k+1) := by omega
          exact ⟨by simpa only [hp] using hb.mpr hlt,hω⟩
      · rintro (hω | hω)
        · exact native_action_freezes π S p q ω (D k+d k) (D (k+1)+d (k+1)) hn.le (false,e) hω
        · exact hω.2
    have hdis : Disjoint E F := by
      apply Set.disjoint_left.mpr
      intro ω hE hF
      have ht := native_return_le π S p q ω (D k+d k) (false,e) hE
      have hn' := hF.1.trans ht
      exact (Nat.not_le_of_gt hn) (WithTop.coe_le_coe.mp hn')
    have hF : MeasurableSet F := by
      let : MeasurableSpace History := ⊤
      have hm := native_execution_measurable π
        (supported_realization σ (batchTable D d a hD hd hc)).1 S p q
      have hh := (hm.1 (D (k+1)+d (k+1)))
        (show MeasurableSet {h : History | h.length = D (k+1)+d (k+1)} from .of_discrete)
      have ha := (hm.2.1 (D (k+1)+d (k+1))) (action_singleton_measurable (.inr (false,e)))
      convert hh.inter ha using 1
      ext ω
      exact and_congr_left (fun _ => (native_full_history_iff π S p q _ ω).symm)
    rw [he, measure_union hdis hF]
    change μ E + μ F = _
    rw [show μ E = bernsteinEval (D k) (d k) (a k e) p q from ih,
      show μ F = bernsteinEval (D (k+1)) (d (k+1)) (exitCoefficients D d a (k+1) e) p q from
        stage_exit_mass D d a hD hd hc S p q (k+1) e]
    exact (add_comm _ _).trans (exit_evaluation_balance D d a hD hd hc p q k e)

end CumulativeOutputs

section LimitLaw
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)
local notation "μ" => rawLaw (rowLaw (batchTable D d a hD hd hc))

/-- The actual eventual output law is the limit of the coefficient evaluations
for the single table, including endpoint source rates. -/
theorem actual_limit_output_mass (S : Bool) (p q : unitInterval) (e : Bool) (L : ℝ≥0∞)
    (hlim : Filter.Tendsto (fun k => bernsteinEval (D k) (d k) (a k e) p q)
      Filter.atTop (nhds L)) :
    μ {ω | ∃ n : ℕ, nativeAction π S p q n ω = .inr (false,e)} = L := by
  let E (k : ℕ) := {ω | nativeAction π S p q (D k+d k) ω = .inr (false,e)}
  have hE : Monotone E := by
    intro i j hij ω hω
    exact native_action_freezes π S p q ω (D i+d i) (D j+d j)
      (Nat.add_le_add (hD.monotone hij) (hd.monotone hij)) (false,e) hω
  have he : {ω | ∃ n : ℕ, nativeAction π S p q n ω = .inr (false,e)} = ⋃ k, E k := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨n,hn⟩
      exact ⟨n,native_action_freezes π S p q ω n (D n+d n)
        ((hD.id_le n).trans (Nat.le_add_right _ _)) (false,e) hn⟩
    · rintro ⟨k,hk⟩
      exact ⟨D k+d k,hk⟩
  have hm : Filter.Tendsto (μ ∘ E) Filter.atTop (nhds (μ (⋃ k, E k))) :=
    tendsto_measure_iUnion_atTop hE
  have hval : (μ ∘ E) = fun k => bernsteinEval (D k) (d k) (a k e) p q := by
    funext k
    exact actual_cumulative_output_mass D d a hD hd hc S p q e k
  rw [he]
  exact tendsto_nhds_unique (by simpa only [hval] using hm) hlim

end LimitLaw

def sourceCalls {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (source : Bool) (ω : Seed × Tape) : WithTop ℕ :=
  ⨆ n : ℕ, (sourceCount source (nativeHistory π S p q n ω) : WithTop ℕ)

private theorem sourceCount_prefix (s : Bool) {h h' : History} (hp : h.IsPrefix h') :
    sourceCount s h ≤ sourceCount s h' := by
  obtain ⟨t,rfl⟩ := hp
  simp only [sourceCount, List.filter_append, List.length_append]
  exact Nat.le_add_right _ _

section SourceCosts
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)

/-- The supremum of actual charged source counts is exactly the returned
batch degree; in a nonreturning execution both actual source counts diverge. -/
theorem actual_source_supremum_at_return (S : Bool) (p q : unitInterval) (ω : RowSeed × Tape) :
    (∀ k, nativeCalls π S p q ω = ((D k+d k : ℕ) : WithTop ℕ) →
      sourceCalls π S p q false ω = (D k : WithTop ℕ) ∧
      sourceCalls π S p q true ω = (d k : WithTop ℕ)) ∧
    (nativeCalls π S p q ω = ⊤ →
      sourceCalls π S p q false ω = ⊤ ∧ sourceCalls π S p q true ω = ⊤) := by
  have hgeom := acquired_history_geometry π S (sourceRead p q) ω
  have hcounts := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.1
  constructor
  · intro k ht
    have hmem := hittingAfter_mem_set_of_ne_top
      (u := nativeAction π S p q) (s := Set.range (fun c : Bool × Bool => (Sum.inr c : Action)))
      (n := 0) (ω := ω) (show nativeCalls π S p q ω ≠ ⊤ by rw [ht]; simp)
    change nativeAction π S p q (nativeCalls π S p q ω).untopA ω ∈ _ at hmem
    rw [ht] at hmem
    obtain ⟨cell,hcell⟩ := hmem
    have hsup (s : Bool) : sourceCalls π S p q s ω =
        (sourceCount s (nativeHistory π S p q (D k+d k) ω) : WithTop ℕ) := by
      apply le_antisymm
      · apply iSup_le
        intro n
        apply WithTop.coe_le_coe.mpr
        by_cases hn : n ≤ D k+d k
        · exact sourceCount_prefix s (hgeom.2.1 n (D k+d k) hn)
        · have he := hgeom.2.2 (D k+d k) cell hcell.symm (n-(D k+d k))
          have hn' : D k+d k+(n-(D k+d k)) = n := by omega
          have he' : nativeHistory π S p q n ω = nativeHistory π S p q (D k+d k) ω := by
            simpa only [hn', nativeHistory] using he
          rw [he']
      · exact le_iSup (fun n : ℕ => (sourceCount s (nativeHistory π S p q n ω) : WithTop ℕ)) (D k+d k)
    exact ⟨(hsup false).trans (congrArg (fun n : ℕ => (n : WithTop ℕ)) (hcounts k ht.ge).1),
      (hsup true).trans (congrArg (fun n : ℕ => (n : WithTop ℕ)) (hcounts k ht.ge).2)⟩
  · intro ht
    have hb (s : Bool) : sourceCalls π S p q s ω = ⊤ := by
      apply WithTop.eq_top_iff_forall_ge.mpr
      intro n
      have hs := hcounts n (by rw [ht]; exact le_top)
      have hh : (n : WithTop ℕ) ≤
          (sourceCount s (nativeHistory π S p q (D n+d n) ω) : WithTop ℕ) := by
        apply WithTop.coe_le_coe.mpr
        cases s
        · rw [hs.1]; exact hD.id_le n
        · rw [hs.2]; exact hd.id_le n
      exact hh.trans (le_iSup (fun m : ℕ =>
        (sourceCount s (nativeHistory π S p q m ω) : WithTop ℕ)) (D n+d n))
    exact ⟨hb false,hb true⟩

/-- Source-tail events and the unresolved landmark event are literally the
same event of the same execution, including nonreturning paths. -/
theorem exact_same_execution_source_tail_events (S : Bool) (p q : unitInterval)
    (ω : RowSeed × Tape) (k : ℕ) :
    ((D k : WithTop ℕ) < sourceCalls π S p q false ω ↔
      ((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω) ∧
    ((d k : WithTop ℕ) < sourceCalls π S p q true ω ↔
      ((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω) := by
  have hN : StrictMono (fun k => D k+d k) := fun x y h => Nat.add_lt_add (hD h) (hd h)
  have hcounters := actual_source_supremum_at_return D d a hD hd hc S p q ω
  cases ht : nativeCalls π S p q ω with
  | top => simp [ht, (hcounters.2 ht).1, (hcounters.2 ht).2]
  | coe n =>
    obtain ⟨j,hj⟩ := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.2 n ht
    have ht' : nativeCalls π S p q ω = ((D j+d j : ℕ) : WithTop ℕ) := by rw [ht, hj]; rfl
    rw [(hcounters.1 j ht').1, (hcounters.1 j ht').2, hj]
    exact ⟨WithTop.coe_lt_coe.trans (hD.lt_iff_lt.trans
      (hN.lt_iff_lt.symm.trans WithTop.coe_lt_coe.symm)),
      WithTop.coe_lt_coe.trans (hd.lt_iff_lt.trans
      (hN.lt_iff_lt.symm.trans WithTop.coe_lt_coe.symm))⟩

end SourceCosts

def sourceWeighted {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (source : Bool) (w : ℕ → ℝ≥0∞) (ω : Seed × Tape) : ℝ≥0∞ :=
  ⨆ n : ℕ, w (sourceCount source (nativeHistory π S p q n ω))

private theorem native_history_after_return {Seed : Type}
    (π : Seed → Bool → History → Action) (S : Bool) (p q : unitInterval)
    (ω : Seed × Tape) (n m : ℕ) (hnm : n ≤ m)
    (ht : nativeCalls π S p q ω ≤ (n : WithTop ℕ)) :
    nativeHistory π S p q m ω = nativeHistory π S p q n ω := by
  obtain ⟨j,hj⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) ht)
  have hj := hj.symm
  have hjn : j ≤ n := by
    rw [hj] at ht
    exact WithTop.coe_le_coe.mp ht
  have hmem := hittingAfter_mem_set_of_ne_top
    (u := nativeAction π S p q) (s := Set.range (fun c : Bool × Bool => (Sum.inr c : Action)))
    (n := 0) (ω := ω) (show nativeCalls π S p q ω ≠ ⊤ by rw [hj]; simp)
  change nativeAction π S p q (nativeCalls π S p q ω).untopA ω ∈ _ at hmem
  rw [hj] at hmem
  obtain ⟨cell,hcell⟩ := hmem
  have hg := (acquired_history_geometry π S (sourceRead p q) ω).2.2 j cell hcell.symm
  have hn' : nativeHistory π S p q n ω = nativeHistory π S p q j ω := by
    simpa only [nativeHistory, Nat.add_sub_of_le hjn] using hg (n-j)
  have hm' : nativeHistory π S p q m ω = nativeHistory π S p q j ω := by
    simpa only [nativeHistory, Nat.add_sub_of_le (hjn.trans hnm)] using hg (m-j)
  exact hm'.trans hn'.symm

section WeightedMoments
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)
local notation "μ" => rawLaw (rowLaw (batchTable D d a hD hd hc))

private theorem actual_weight_step (S : Bool) (p q : unitInterval) (source : Bool)
    (w : ℕ → ℝ≥0∞) (k : ℕ) (ω : RowSeed × Tape) :
    w (sourceCount source (nativeHistory π S p q (D (k+1)+d (k+1)) ω)) -
      w (sourceCount source (nativeHistory π S p q (D k+d k) ω)) =
    if ((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω then
      w (if source then d (k+1) else D (k+1)) - w (if source then d k else D k) else 0 := by
  have hn : D k+d k < D (k+1)+d (k+1) := Nat.add_lt_add
    (hD (Nat.lt_succ_self k)) (hd (Nat.lt_succ_self k))
  by_cases ht : ((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω
  · rw [if_pos ht]
    have hnext := (actual_between_landmarks D d a hD hd hc S p q ω k
      (D (k+1)+d (k+1)-1) (by omega) (by omega)).2.1
    have hp : D (k+1)+d (k+1)-1+1 = D (k+1)+d (k+1) := by omega
    have hreach : ((D (k+1)+d (k+1) : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω := by
      simpa only [hp] using hnext.mpr ht
    have h0 := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.1 k ht.le
    have h1 := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.1 (k+1) hreach
    cases source <;> simp only [h0.1,h0.2,h1.1,h1.2,Bool.false_eq_true,↓reduceIte]
  · rw [if_neg ht, native_history_after_return π S p q ω (D k+d k) (D (k+1)+d (k+1)) hn.le
      (le_of_not_gt ht), tsub_self]

private theorem finite_actual_weight_telescope (S : Bool) (p q : unitInterval) (source : Bool)
    (w : ℕ → ℝ≥0∞) (hw : Monotone w) (J : ℕ) (ω : RowSeed × Tape) :
    w (sourceCount source (nativeHistory π S p q (D J+d J) ω)) =
      w (if source then d 0 else D 0) + ∑ k ∈ Finset.range J,
        if ((if source then d k else D k : ℕ) : WithTop ℕ) < sourceCalls π S p q source ω then
          w (if source then d (k+1) else D (k+1)) - w (if source then d k else D k) else 0 := by
  have htail (k : ℕ) :
      (((if source then d k else D k : ℕ) : WithTop ℕ) < sourceCalls π S p q source ω) ↔
      (((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω) := by
    cases source
    · exact (exact_same_execution_source_tail_events D d a hD hd hc S p q ω k).1
    · exact (exact_same_execution_source_tail_events D d a hD hd hc S p q ω k).2
  simp_rw [htail, ← actual_weight_step D d a hD hd hc S p q source w]
  let V (k : ℕ) := w (sourceCount source (nativeHistory π S p q (D k+d k) ω))
  have hm : Monotone V := by
    intro i j hij
    exact hw (sourceCount_prefix source ((acquired_history_geometry π S (sourceRead p q) ω).2.1
      (D i+d i) (D j+d j) (Nat.add_le_add (hD.monotone hij) (hd.monotone hij))))
  have htel (n : ℕ) : V 0 + ∑ k ∈ Finset.range n, (V (k+1)-V k) = V n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih, add_tsub_cancel_of_le (hm (Nat.le_succ n))]
  have h0 := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.1 0
    (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.1
  have he : V 0 = w (if source then d 0 else D 0) := by
    cases source <;> simp only [V,h0.1,h0.2,Bool.false_eq_true,↓reduceIte]
  exact (htel J).symm.trans (by rw [he])

private theorem infinite_actual_weight_telescope (S : Bool) (p q : unitInterval) (source : Bool)
    (w : ℕ → ℝ≥0∞) (hw : Monotone w) (ω : RowSeed × Tape) :
    sourceWeighted π S p q source w ω = w (if source then d 0 else D 0) +
      ∑' k : ℕ, if ((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω then
        w (if source then d (k+1) else D (k+1)) - w (if source then d k else D k) else 0 := by
  have hcofinal : sourceWeighted π S p q source w ω =
      ⨆ k : ℕ, w (sourceCount source (nativeHistory π S p q (D k+d k) ω)) := by
    apply le_antisymm
    · apply iSup_le
      intro n
      apply le_iSup_of_le n
      exact hw (sourceCount_prefix source ((acquired_history_geometry π S (sourceRead p q) ω).2.1
        n (D n+d n) ((hD.id_le n).trans (Nat.le_add_right _ _))))
    · apply iSup_le
      intro k
      exact le_iSup (fun n : ℕ => w (sourceCount source (nativeHistory π S p q n ω))) (D k+d k)
  rw [hcofinal, ENNReal.tsum_eq_iSup_nat, ENNReal.add_iSup]
  apply iSup_congr
  intro J
  have ht := finite_actual_weight_telescope D d a hD hd hc S p q source w hw J ω
  have he (k : ℕ) :
      (((if source then d k else D k : ℕ) : WithTop ℕ) < sourceCalls π S p q source ω) ↔
      (((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω) := by
    cases source
    · exact (exact_same_execution_source_tail_events D d a hD hd hc S p q ω k).1
    · exact (exact_same_execution_source_tail_events D d a hD hd hc S p q ω k).2
  simpa only [he] using ht

/-- The source moment is the integral of powers of the supremum of actual
acquired counts. Its tail sum is valid in extended nonnegative reals, whether
finite or infinite. -/
private theorem weighted_source_moment_sum (S : Bool) (p q : unitInterval)
    (source : Bool) (s : ℝ) (hs : 0 ≤ s) :
    (∫⁻ ω, sourceWeighted π S p q source (fun n => (n : ℝ≥0∞)^s) ω ∂μ) =
      ((if source then d 0 else D 0 : ℕ) : ℝ≥0∞)^s +
      ∑' k : ℕ, (((if source then d (k+1) else D (k+1) : ℕ) : ℝ≥0∞)^s -
        ((if source then d k else D k : ℕ) : ℝ≥0∞)^s) *
          bernsteinEval (D k) (d k) (residualCoefficients D d a k) p q := by
  have := NativeBernoulliFactoryCriticalMoment.uniform_probability
  let : IsProbabilityMeasure μ := by unfold rawLaw rowLaw; infer_instance
  let w := fun n : ℕ => (n : ℝ≥0∞)^s
  have hw : Monotone w := fun i j hij => ENNReal.rpow_le_rpow (by exact_mod_cast hij) hs
  let E (k : ℕ) := {ω | ((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω}
  let c (k : ℕ) := w (if source then d (k+1) else D (k+1)) - w (if source then d k else D k)
  have hE (k : ℕ) : MeasurableSet (E k) := (native_execution_measurable π
    (supported_realization σ (batchTable D d a hD hd hc)).1 S p q).2.2 (D k+d k)
  have hpoint (ω : RowSeed × Tape) : sourceWeighted π S p q source w ω =
      w (if source then d 0 else D 0) + ∑' k : ℕ, (E k).indicator (fun _ => c k) ω := by
    simpa only [Set.indicator, E, Set.mem_ofPred_eq, c] using
      infinite_actual_weight_telescope D d a hD hd hc S p q source w hw ω
  change (∫⁻ ω, sourceWeighted π S p q source w ω ∂μ) = _
  simp_rw [hpoint]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_tsum (fun k => (measurable_const.indicator (hE k)).aemeasurable)]
  congr 1
  apply tsum_congr
  intro k
  rw [lintegral_indicator_const (hE k), actual_unresolved_mass D d a hD hd hc S p q k]

end WeightedMoments

def sourcePower {Seed : Type} (π : Seed → Bool → History → Action) (S : Bool)
    (p q : unitInterval) (source : Bool) (s : ℝ) (ω : Seed × Tape) : ℝ≥0∞ :=
  if sourceCalls π S p q source ω = ⊤ then ⊤ else
    (((sourceCalls π S p q source ω).untopD 0 : ℕ) : ℝ≥0∞)^s

section PowerBridge
variable (D d : ℕ → ℕ) (a : CoefficientFamily D d)
  (hD : StrictMono D) (hd : StrictMono d) (hc : CompatibleCoefficients D d a)
local notation "σ" => fixedSchedule D d hD hd
local notation "π" => safePolicy σ (batchTable D d a hD hd hc)
local notation "μ" => rawLaw (rowLaw (batchTable D d a hD hd hc))

private theorem source_power_is_actual_counter_power (S : Bool) (p q : unitInterval)
    (source : Bool) (s : ℝ) (hs : 0 < s) (ω : RowSeed × Tape) :
    sourceWeighted π S p q source (fun n => (n : ℝ≥0∞)^s) ω = sourcePower π S p q source s ω := by
  have hcounters := actual_source_supremum_at_return D d a hD hd hc S p q ω
  cases ht : nativeCalls π S p q ω with
  | top =>
    have hc' : sourceCalls π S p q source ω = ⊤ := by
      cases source
      · exact (hcounters.2 ht).1
      · exact (hcounters.2 ht).2
    simp only [sourcePower,hc',↓reduceIte]
    apply top_unique
    have hp : (⨆ n : ℕ, (n : ℝ≥0∞)^s) = ⊤ := by
      have hh := (ENNReal.orderIsoRpow s hs).map_iSup (fun n : ℕ => (n : ℝ≥0∞))
      simpa only [ENNReal.orderIsoRpow_apply, ENNReal.iSup_natCast,
        ENNReal.top_rpow_of_pos hs] using hh.symm
    rw [← hp]
    apply iSup_le
    intro n
    have hcount := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.1 n
      (by rw [ht]; exact le_top)
    apply le_iSup_of_le (D n+d n)
    apply ENNReal.rpow_le_rpow _ hs.le
    apply Nat.cast_le.mpr
    cases source
    · rw [hcount.1]; exact hD.id_le n
    · rw [hcount.2]; exact hd.id_le n
  | coe n =>
    obtain ⟨k,hk⟩ := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.2 n ht
    have ht' : nativeCalls π S p q ω = ((D k+d k : ℕ) : WithTop ℕ) := by rw [ht, hk]; rfl
    let M := if source then d k else D k
    have hM : sourceCalls π S p q source ω = (M : WithTop ℕ) := by
      cases source
      · exact (hcounters.1 k ht').1
      · exact (hcounters.1 k ht').2
    simp only [sourcePower,hM,WithTop.natCast_ne_top,↓reduceIte,WithTop.untopD_natCast, Nat.cast_id]
    apply le_antisymm
    · apply iSup_le
      intro m
      have hh := le_iSup (fun m : ℕ =>
        (sourceCount source (nativeHistory π S p q m ω) : WithTop ℕ)) m
      change (sourceCount source (nativeHistory π S p q m ω) : WithTop ℕ) ≤
        sourceCalls π S p q source ω at hh
      rw [hM] at hh
      exact ENNReal.rpow_le_rpow (Nat.cast_le.mpr (WithTop.coe_le_coe.mp hh)) hs.le
    · have hcounts := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.1 k ht'.ge
      have he : sourceCount source (nativeHistory π S p q (D k+d k) ω) = M := by
        cases source
        · exact hcounts.1
        · exact hcounts.2
      have hh := le_iSup (fun m : ℕ =>
        (sourceCount source (nativeHistory π S p q m ω) : ℝ≥0∞)^s) (D k+d k)
      rw [he] at hh
      exact hh

private theorem actual_single_layer_moment_lower_bound (S : Bool) (p q : unitInterval)
    (source : Bool) (s : ℝ) (hs : 0 < s) (k : ℕ) :
    ((if source then d (k+1) else D (k+1) : ℕ) : ℝ≥0∞)^s *
      bernsteinEval (D k) (d k) (residualCoefficients D d a k) p q ≤
      ∫⁻ ω, sourcePower π S p q source s ω ∂μ := by
  let E := {ω | ((D k+d k : ℕ) : WithTop ℕ) < nativeCalls π S p q ω}
  let c : ℝ≥0∞ := ((if source then d (k+1) else D (k+1) : ℕ) : ℝ≥0∞)^s
  have hE : MeasurableSet E := (native_execution_measurable π
    (supported_realization σ (batchTable D d a hD hd hc)).1 S p q).2.2 (D k+d k)
  rw [← actual_unresolved_mass D d a hD hd hc S p q k]
  change c * μ E ≤ _
  rw [← lintegral_indicator_const hE c]
  apply lintegral_mono
  intro ω
  by_cases ht : ω ∈ E
  · rw [Set.indicator_of_mem ht, ← source_power_is_actual_counter_power D d a hD hd hc S p q source s hs ω]
    have hn : D k+d k < D (k+1)+d (k+1) := Nat.add_lt_add
      (hD (Nat.lt_succ_self k)) (hd (Nat.lt_succ_self k))
    have hb := (actual_between_landmarks D d a hD hd hc S p q ω k
      (D (k+1)+d (k+1)-1) (by omega) (by omega)).2.1
    have hp : D (k+1)+d (k+1)-1+1 = D (k+1)+d (k+1) := by omega
    have hreach : ((D (k+1)+d (k+1) : ℕ) : WithTop ℕ) ≤ nativeCalls π S p q ω := by
      simpa only [hp] using hb.mpr ht
    have hcount := (actual_schedule_and_return_landmarks D d a hD hd hc S p q ω).2.2.1 (k+1) hreach
    have he : sourceCount source (nativeHistory π S p q (D (k+1)+d (k+1)) ω) =
        if source then d (k+1) else D (k+1) := by
      cases source
      · exact hcount.1
      · exact hcount.2
    have hh := le_iSup (fun n : ℕ =>
      (sourceCount source (nativeHistory π S p q n ω) : ℝ≥0∞)^s) (D (k+1)+d (k+1))
    rw [he] at hh
    exact hh
  · rw [Set.indicator_of_notMem ht]
    exact bot_le

/-- The exact actual-counter moment has its extended tail-sum formula and
simultaneously dominates every next-batch cost times the actual survivor mass. -/
theorem actual_finite_and_infinite_moment_sums (S : Bool) (p q : unitInterval)
    (source : Bool) (s : ℝ) (hs : 0 < s) :
    (∫⁻ ω, sourcePower π S p q source s ω ∂μ) =
      ((if source then d 0 else D 0 : ℕ) : ℝ≥0∞)^s +
      ∑' k : ℕ, (((if source then d (k+1) else D (k+1) : ℕ) : ℝ≥0∞)^s -
        ((if source then d k else D k : ℕ) : ℝ≥0∞)^s) *
          bernsteinEval (D k) (d k) (residualCoefficients D d a k) p q ∧
    ∀ k : ℕ, ((if source then d (k+1) else D (k+1) : ℕ) : ℝ≥0∞)^s *
      bernsteinEval (D k) (d k) (residualCoefficients D d a k) p q ≤
        ∫⁻ ω, sourcePower π S p q source s ω ∂μ := by
  constructor
  · have hh := weighted_source_moment_sum D d a hD hd hc S p q source s hs.le
    simpa only [source_power_is_actual_counter_power D d a hD hd hc S p q source s hs] using hh
  · exact actual_single_layer_moment_lower_bound D d a hD hd hc S p q source s hs

end PowerBridge

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinStageMass
