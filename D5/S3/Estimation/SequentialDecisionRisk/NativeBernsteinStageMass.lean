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

end D5.S3.Estimation.SequentialDecisionRisk.NativeBernsteinStageMass
