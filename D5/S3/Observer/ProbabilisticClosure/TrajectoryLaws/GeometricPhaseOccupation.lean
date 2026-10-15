/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/GeometricPhaseOccupation
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/GeometricPhaseOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Discounted occupation of a phase-only geometric advancement chain. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass
import D5.S3.Analytic.PrimeProducts.GeometricResidualMemorylessness
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Classical
open MeasureTheory ProbabilityTheory Finset Preorder
open scoped NNReal ENNReal BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.GeometricPhaseOccupation

/-- Index zero denotes the first live phase. -/
def success (n : ℕ) : ℝ≥0 := (1 / 2) ^ (n + 1)

private lemma success_le_one (n : ℕ) : success n ≤ 1 := by
  unfold success
  exact pow_le_one₀ (by norm_num) (by norm_num)

def parameter (n : ℕ) : unitInterval :=
  ⟨success n, (success n).coe_nonneg, by exact_mod_cast success_le_one n⟩

/-- One actual zero makes one coin transition, retaining only the phase. -/
def zeroRow (n : ℕ) : PMF ℕ :=
  (PMF.bernoulli (success n) (success_le_one n)).map fun b => if b then n + 1 else n

def phaseLaw : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | k + 1 => (phaseLaw k).bind zeroRow

/-- The index J is dead; the live indices are 0 through J-1. -/
def cappedRow (J n : ℕ) : PMF ℕ :=
  if n < J then (zeroRow n).map (fun t => min t J) else PMF.pure J

private lemma zero_row_apply (n t : ℕ) :
    zeroRow n t = (if t = n then (↑(1 - success n) : ℝ≥0∞) else 0) +
      (if t = n + 1 then (↑(success n) : ℝ≥0∞) else 0) := by
  simp [zeroRow, PMF.map_apply, tsum_fintype, PMF.bernoulli_apply, ENNReal.coe_sub, add_comm]

private lemma cap_zero_row (J n : ℕ) :
    (zeroRow n).map (fun t => min t J) = cappedRow J (min n J) := by
  by_cases h : n < J
  · simp [cappedRow, Nat.min_eq_left h.le, h]
  · have hn : J ≤ n := Nat.le_of_not_gt h
    have hs : min n J = J := Nat.min_eq_right hn
    simp only [cappedRow, hs, lt_self_iff_false, ↓reduceIte]
    rw [zeroRow, PMF.map_comp]
    have hf : ((fun t => min t J) ∘ (fun b : Bool => if b then n + 1 else n)) =
        Function.const Bool J := by
      funext b
      cases b <;> simp [Nat.min_eq_right hn, Nat.min_eq_right (by omega : J ≤ n + 1)]
    rw [hf, PMF.map_const]

/-- The analytical holding variable counts failures before its successful zero. -/
def failures (j : ℕ) : PMF ℕ := (geometricMeasure (parameter j)).toPMF

/-- Entrance into phase j+1, as a sum of j independent positive holding times. -/
def entranceLaw : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | j + 1 => (entranceLaw j).bind fun t => (failures j).map fun w => t + w + 1

def renewalMass (j k : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ range (k + 1), entranceLaw j t * (↑(1 - success j) : ℝ≥0∞) ^ (k - t)

private lemma parameter_ne_zero (j : ℕ) : parameter j ≠ 0 := by
  intro h
  have he : (success j : ℝ) = 0 := congrArg Subtype.val h
  have hp : (0 : ℝ) < success j := by
    change 0 < (1 / 2 : ℝ) ^ (j + 1)
    positivity
  exact hp.ne' he

private lemma failures_apply (j w : ℕ) :
    failures j w = (↑(1 - success j) : ℝ≥0∞) ^ w * ↑(success j) := by
  rw [failures, Measure.toPMF_apply, geometricMeasure_singleton (parameter_ne_zero j)]
  have he : (1 - (parameter j : ℝ)) ^ w * (parameter j : ℝ) =
      (((1 - success j) ^ w * success j : ℝ≥0) : ℝ) := by
    simp [parameter, NNReal.coe_sub (success_le_one j)]
  rw [he, ENNReal.ofReal_coe_nnreal]
  simp

private lemma holding_shift_apply (j t k : ℕ) :
    ((failures j).map fun w => t + w + 1) (k + 1) =
      if t ≤ k then failures j (k - t) else 0 := by
  rw [PMF.map_apply]
  by_cases h : t ≤ k
  · rw [if_pos h, tsum_eq_single (k - t)]
    · simp [show k + 1 = t + (k - t) + 1 by omega]
    · intro w hw
      have he : k + 1 ≠ t + w + 1 := by omega
      simp only [if_neg he]
  · rw [if_neg h]
    apply ENNReal.tsum_eq_zero.mpr
    intro w
    have he : k + 1 ≠ t + w + 1 := by omega
    simp only [if_neg he]

private lemma entrance_zero (j : ℕ) : entranceLaw (j + 1) 0 = 0 := by
  simp only [entranceLaw, PMF.bind_apply, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro t
  simp

private lemma entrance_succ (j k : ℕ) :
    entranceLaw (j + 1) (k + 1) = renewalMass j k * ↑(success j) := by
  simp only [entranceLaw, PMF.bind_apply, holding_shift_apply]
  rw [tsum_eq_sum (s := range (k + 1))]
  · rw [renewalMass, sum_mul]
    apply sum_congr rfl
    intro t ht
    rw [if_pos (Nat.le_of_lt_succ (mem_range.mp ht)), failures_apply]
    exact (mul_assoc _ _ _).symm
  · intro t ht
    have h : ¬t ≤ k := by simpa only [mem_range, Nat.lt_succ_iff] using ht
    simp [h]

private lemma renewal_succ (j k : ℕ) :
    renewalMass j (k + 1) = renewalMass j k * ↑(1 - success j) +
      entranceLaw j (k + 1) := by
  unfold renewalMass
  rw [sum_range_succ, sum_mul]
  simp only [Nat.sub_self, pow_zero, mul_one]
  congr 1
  apply sum_congr rfl
  intro t ht
  have he : k + 1 - t = (k - t) + 1 := by
    have := mem_range.mp ht
    omega
  rw [he, pow_succ, mul_assoc]

private lemma renewal_zero_phase (k : ℕ) :
    renewalMass 0 k = (↑(1 - success 0) : ℝ≥0∞) ^ k := by
  simp [renewalMass, entranceLaw, PMF.pure_apply]

private lemma renewal_zero_time (j : ℕ) : renewalMass (j + 1) 0 = 0 := by
  simp [renewalMass, entrance_zero]

private lemma actual_zero_phase (k : ℕ) :
    phaseLaw (k + 1) 0 = phaseLaw k 0 * ↑(1 - success 0) := by
  simp only [phaseLaw, PMF.bind_apply, zero_row_apply]
  simp [mul_ite]

private lemma actual_succ_phase (j k : ℕ) :
    phaseLaw (k + 1) (j + 1) =
      phaseLaw k (j + 1) * ↑(1 - success (j + 1)) + phaseLaw k j * ↑(success j) := by
  simp only [phaseLaw, PMF.bind_apply, zero_row_apply, mul_add]
  rw [ENNReal.tsum_add]
  simp [mul_ite]

private theorem actual_renewal_mass (k j : ℕ) : phaseLaw k j = renewalMass j k := by
  induction k generalizing j with
  | zero =>
    cases j with
    | zero => simp [phaseLaw, renewal_zero_phase]
    | succ j => simp [phaseLaw, renewal_zero_time, PMF.pure_apply]
  | succ k ih =>
    cases j with
    | zero =>
      rw [actual_zero_phase, ih, renewal_zero_phase, renewal_zero_phase, pow_succ]
    | succ j =>
      rw [actual_succ_phase, ih, ih, renewal_succ, entrance_succ]

/-- An independent current holding variable paired with its entrance count. -/
def intervalLaw (j : ℕ) : PMF (ℕ × ℕ) :=
  (entranceLaw j).bind fun t => (failures j).map fun w => (t, w)

def intervalMass (j k : ℕ) : ℝ≥0∞ :=
  (intervalLaw j).toMeasure {tw | tw.1 ≤ k ∧ k < tw.1 + tw.2 + 1}

private theorem interval_mass_eq_renewal (j k : ℕ) : intervalMass j k = renewalMass j k := by
  unfold intervalMass intervalLaw
  rw [PMF.toMeasure_bind_apply _ _ _ MeasurableSet.of_discrete]
  have he (t : ℕ) :
      (((failures j).map fun w => (t, w)).toMeasure
        {tw | tw.1 ≤ k ∧ k < tw.1 + tw.2 + 1}) =
        if t ≤ k then (↑(1 - success j) : ℝ≥0∞) ^ (k - t) else 0 := by
    rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) MeasurableSet.of_discrete]
    by_cases h : t ≤ k
    · rw [if_pos h]
      have hp : (fun w : ℕ => (t, w)) ⁻¹' {tw | tw.1 ≤ k ∧ k < tw.1 + tw.2 + 1}
          = Set.Ici (k - t) := by
        ext w
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ici]
        omega
      rw [hp, failures, Measure.toPMF_toMeasure,
        D5.S3.Analytic.PrimeProducts.GeometricResidualMemorylessness.geometric_tail_mass
          (parameter j) (parameter_ne_zero j)]
      have hc : (1 - (parameter j : ℝ)) ^ (k - t) =
          (((1 - success j) ^ (k - t) : ℝ≥0) : ℝ) := by
        simp [parameter, NNReal.coe_sub (success_le_one j)]
      rw [hc, ENNReal.ofReal_coe_nnreal]
      simp
    · have hp : (fun w : ℕ => (t, w)) ⁻¹' {tw | tw.1 ≤ k ∧ k < tw.1 + tw.2 + 1}
          = ∅ := by ext w; simp [h]
      simp [h]
  simp_rw [he]
  rw [tsum_eq_sum (s := range (k + 1))]
  · apply sum_congr rfl
    intro t ht
    rw [if_pos (Nat.le_of_lt_succ (mem_range.mp ht))]
  · intro t ht
    have h : ¬t ≤ k := by simpa only [mem_range, Nat.lt_succ_iff] using ht
    simp [h]

/-- The actual path measure is generated directly by the phase-only row. -/
def phaseKernel : Kernel ℕ ℕ := Kernel.ofFunOfCountable fun j => (zeroRow j).toMeasure

instance : IsMarkovKernel phaseKernel :=
  ⟨fun j => inferInstanceAs (IsProbabilityMeasure (zeroRow j).toMeasure)⟩

def trajectoryLaw : Measure (ℕ → ℕ) :=
  Kernel.trajMeasure (X := fun _ => ℕ) (Measure.dirac 0) (fun n =>
    phaseKernel.comap (fun u : Iic n → ℕ => u ⟨n, mem_Iic.2 le_rfl⟩)
      (measurable_pi_apply _))

instance : IsProbabilityMeasure trajectoryLaw := by unfold trajectoryLaw; infer_instance

private theorem native_marginal (k : ℕ) :
    trajectoryLaw.map (fun x => x k) = (phaseLaw k).toMeasure := by
  induction k with
  | zero =>
    apply Measure.ext_of_singleton
    intro j
    have h := MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton
      (Measure.dirac 0) phaseKernel 0 (fun _ => j)
    change (trajectoryLaw.map (fun x i => x (i : Fin 1))) {fun _ => j} = _ at h
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    have he : (fun (x : ℕ → ℕ) (i : Fin 1) => x i) ⁻¹' {fun _ => j} =
        (fun x : ℕ → ℕ => x 0) ⁻¹' {j} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
      exact ⟨fun hx => hx 0, fun hx i => by simpa using hx⟩
    rw [he] at h
    simpa [phaseLaw, PMF.toMeasure_pure] using h
  | succ k ih =>
    let step : Kernel (Iic k → ℕ) ℕ :=
      phaseKernel.comap (fun u => u ⟨k, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)
    have hpair : trajectoryLaw.map (frestrictLe k) ⊗ₘ step =
        trajectoryLaw.map (fun x => (frestrictLe k x, x (k + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have hnext : trajectoryLaw.map (fun x => x (k + 1)) =
        step ∘ₘ (trajectoryLaw.map (frestrictLe k)) := by
      rw [← Measure.snd_compProd]
      change _ = (trajectoryLaw.map (frestrictLe k) ⊗ₘ step).map Prod.snd
      rw [hpair, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [hnext]
    apply Measure.ext_of_singleton
    intro j
    rw [Measure.bind_apply (measurableSet_singleton _) step.aemeasurable,
      lintegral_map (step.measurable_coe (measurableSet_singleton _))
        (measurable_frestrictLe k)]
    change (∫⁻ x, (zeroRow (x k)).toMeasure {j} ∂trajectoryLaw) = _
    rw [← lintegral_map (measurable_of_countable (fun n => (zeroRow n).toMeasure {j}))
      (measurable_pi_apply k), ih, lintegral_countable']
    simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rw [phaseLaw, PMF.bind_apply]
    apply tsum_congr
    intro n
    exact mul_comm _ _

private theorem actual_interval_occupation (j k : ℕ) :
    trajectoryLaw {x | x k = j} = intervalMass j k := by
  have h := congrArg (fun μ : Measure ℕ => μ {j}) (native_marginal k)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at h
  change trajectoryLaw ((fun x => x k) ⁻¹' {j}) = _
  rw [h, actual_renewal_mass, interval_mass_eq_renewal]

def actualOccupation (weight : ℕ → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ∑' k : ℕ, if x k = j then weight k else 0 ∂trajectoryLaw

/-- The upper endpoint is entrance plus failures plus the successful zero. -/
def analyticalOccupation (weight : ℕ → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  ∫⁻ tw, ∑ k ∈ Ico (max 1 tw.1) (tw.1 + tw.2 + 1), weight k ∂(intervalLaw j).toMeasure

private lemma interval_sum_as_tsum (weight : ℕ → ℝ≥0∞) (hzero : weight 0 = 0)
    (tw : ℕ × ℕ) :
    (∑ k ∈ Ico (max 1 tw.1) (tw.1 + tw.2 + 1), weight k) =
      ∑' k : ℕ, if tw.1 ≤ k ∧ k < tw.1 + tw.2 + 1 then weight k else 0 := by
  rw [tsum_eq_sum (s := Ico (max 1 tw.1) (tw.1 + tw.2 + 1))]
  · apply sum_congr rfl
    intro k hk
    have h := mem_Ico.mp hk
    rw [if_pos ⟨by omega, h.2⟩]
  · intro k hk
    by_cases hc : tw.1 ≤ k ∧ k < tw.1 + tw.2 + 1
    · have h0 : k = 0 := by
        have hn : ¬(max 1 tw.1 ≤ k ∧ k < tw.1 + tw.2 + 1) := by simpa using hk
        omega
      simp [h0, hzero]
    · simp only [if_neg hc]

private theorem actual_occupation_series (weight : ℕ → ℝ≥0∞) (j : ℕ) :
    actualOccupation weight j = ∑' k : ℕ, weight k * trajectoryLaw {x | x k = j} := by
  unfold actualOccupation
  have hm (k : ℕ) : MeasurableSet {x : ℕ → ℕ | x k = j} :=
    (measurableSet_singleton j).preimage (measurable_pi_apply k)
  rw [lintegral_tsum]
  · apply tsum_congr
    intro k
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, setLIntegral_const] using
      (lintegral_indicator (μ := trajectoryLaw) (f := fun _ => weight k) (hm k))
  · intro k
    exact (Measurable.ite (hm k) measurable_const measurable_const).aemeasurable

private theorem analytical_occupation_series (weight : ℕ → ℝ≥0∞)
    (hzero : weight 0 = 0) (j : ℕ) :
    analyticalOccupation weight j = ∑' k : ℕ, weight k * intervalMass j k := by
  unfold analyticalOccupation
  simp_rw [interval_sum_as_tsum weight hzero]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro k
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, setLIntegral_const, intervalMass] using
      (lintegral_indicator (μ := (intervalLaw j).toMeasure) (f := fun _ => weight k)
        (MeasurableSet.of_discrete : MeasurableSet
          {tw : ℕ × ℕ | tw.1 ≤ k ∧ k < tw.1 + tw.2 + 1}))
  · intro k
    exact (measurable_of_countable _).aemeasurable

private theorem actual_analytical_occupation (weight : ℕ → ℝ≥0∞)
    (hzero : weight 0 = 0) (j : ℕ) :
    actualOccupation weight j = analyticalOccupation weight j := by
  rw [actual_occupation_series, analytical_occupation_series weight hzero]
  apply tsum_congr
  intro k
  rw [actual_interval_occupation]

/-- The last element is the sole dead state. -/
def capState (J n : ℕ) : Fin (J + 1) := ⟨min n J, by omega⟩

def finiteCappedRow (J : ℕ) (z : Fin (J + 1)) : PMF (Fin (J + 1)) :=
  (cappedRow J z.val).map (capState J)

def finiteCappedLaw (J : ℕ) : ℕ → PMF (Fin (J + 1))
  | 0 => PMF.pure ⟨0, by omega⟩
  | k + 1 => (finiteCappedLaw J k).bind (finiteCappedRow J)

private lemma finite_cap_zero_row (J n : ℕ) :
    (zeroRow n).map (capState J) = finiteCappedRow J (capState J n) := by
  have hh := congrArg (fun p : PMF ℕ => p.map (capState J)) (cap_zero_row J n)
  rw [PMF.map_comp] at hh
  have he : (capState J ∘ fun t => min t J) = capState J := by
    funext t
    apply Fin.ext
    simp [capState]
  rw [he] at hh
  exact hh

private lemma finite_cap_phase_law (J k : ℕ) :
    (phaseLaw k).map (capState J) = finiteCappedLaw J k := by
  induction k with
  | zero => simp [phaseLaw, finiteCappedLaw, PMF.pure_map, capState]
  | succ k ih =>
    simp only [phaseLaw, finiteCappedLaw, PMF.map_bind, ← ih, PMF.bind_map]
    congr 1
    funext n
    exact finite_cap_zero_row J n

private lemma finite_capped_live_mass (J j k : ℕ) (hj : j < J) :
    finiteCappedLaw J k ⟨j, by omega⟩ = phaseLaw k j := by
  rw [← finite_cap_phase_law, PMF.map_apply]
  have he (n : ℕ) : (⟨j, by omega⟩ : Fin (J + 1)) = capState J n ↔ j = n := by
    simp only [Fin.ext_iff, capState]
    omega
  simp_rw [he]
  simp

private theorem finite_capped_live_occupation (weight : ℕ → ℝ≥0∞)
    (J j : ℕ) (hj : j < J) :
    (∑' k : ℕ, weight k * finiteCappedLaw J k ⟨j, by omega⟩) =
      actualOccupation weight j := by
  rw [actual_occupation_series]
  apply tsum_congr
  intro k
  rw [finite_capped_live_mass J j k hj]
  have hm := congrArg (fun μ : Measure ℕ => μ {j}) (native_marginal k)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at hm
  change weight k * phaseLaw k j = weight k * trajectoryLaw ((fun x => x k) ⁻¹' {j})
  rw [hm]

def natMoment (μ : PMF ℕ) (p : ℕ) : ℝ≥0∞ := ∑' n : ℕ, μ n * (n : ℝ≥0∞) ^ p

def holdingMoment (j p : ℕ) : ℝ≥0∞ :=
  ∑' w : ℕ, failures j w * ((w + 1 : ℕ) : ℝ≥0∞) ^ p

private lemma success_pos (j : ℕ) : 0 < success j := by
  unfold success
  positivity

private lemma success_inv (j : ℕ) : (↑(success j) : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞) ^ (j + 1) := by
  norm_num [success, ENNReal.coe_pow, ENNReal.coe_div, ENNReal.inv_pow]

private lemma geometric_choose_sum (j p : ℕ) :
    (∑' w : ℕ, ((w + p).choose p : ℝ≥0∞) * (↑(1 - success j) : ℝ≥0∞) ^ w) =
      (↑(success j) : ℝ≥0∞)⁻¹ ^ (p + 1) := by
  have hp : (0 : ℝ) < success j := by exact_mod_cast success_pos j
  have hq : ‖(1 - (success j : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · linarith
    · exact sub_nonneg.mpr (by exact_mod_cast success_le_one j)
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one p hq
  have hn : HasSum (fun w : ℕ => ((w + p).choose p : ℝ≥0) * (1 - success j) ^ w)
      ((success j)⁻¹ ^ (p + 1)) := by
    apply NNReal.hasSum_coe.mp
    simpa [NNReal.coe_sub (success_le_one j), one_div, inv_pow] using hs
  simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_pow,
    ENNReal.coe_inv (success_pos j).ne'] using
    (ENNReal.hasSum_coe.mpr hn).tsum_eq

private lemma holding_moment_bound (j p : ℕ) :
    holdingMoment j p ≤ (p.factorial : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (j + 1)) ^ p := by
  unfold holdingMoment
  simp_rw [failures_apply]
  have hp0 : (↑(success j) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (success_pos j).ne'
  have hc : (↑(success j) : ℝ≥0∞) * (↑(success j) : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hp0 ENNReal.coe_ne_top
  calc
    (∑' w : ℕ, (↑(1 - success j) : ℝ≥0∞) ^ w * ↑(success j) * ((w + 1 : ℕ) : ℝ≥0∞) ^ p)
      ≤ ∑' w : ℕ, (↑(1 - success j) : ℝ≥0∞) ^ w * ↑(success j) *
          ((p.factorial : ℝ≥0∞) * ((w + p).choose p : ℝ≥0∞)) := by
        apply ENNReal.tsum_le_tsum
        intro w
        apply mul_le_mul_right
        exact_mod_cast (Nat.pow_succ_le_ascFactorial (w + 1) p).trans_eq
          (Nat.ascFactorial_eq_factorial_mul_choose w p)
    _ = (p.factorial : ℝ≥0∞) * ↑(success j) *
        ∑' w : ℕ, ((w + p).choose p : ℝ≥0∞) * (↑(1 - success j) : ℝ≥0∞) ^ w := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro w
      ac_rfl
    _ = (p.factorial : ℝ≥0∞) * (↑(success j) : ℝ≥0∞)⁻¹ ^ p := by
      rw [geometric_choose_sum, pow_succ]
      calc
        (p.factorial : ℝ≥0∞) * ↑(success j) *
            ((↑(success j) : ℝ≥0∞)⁻¹ ^ p * (↑(success j) : ℝ≥0∞)⁻¹)
          = (p.factorial : ℝ≥0∞) *
              ((↑(success j) : ℝ≥0∞) * (↑(success j) : ℝ≥0∞)⁻¹) *
              (↑(success j) : ℝ≥0∞)⁻¹ ^ p := by ac_rfl
        _ = _ := by rw [hc, mul_one]
    _ = _ := by rw [success_inv]

private lemma nat_moment_zero (μ : PMF ℕ) : natMoment μ 0 = 1 := by
  simpa [natMoment] using μ.tsum_coe

private lemma nat_moment_map (μ : PMF ℕ) (f : ℕ → ℕ) (p : ℕ) :
    natMoment (μ.map f) p = ∑' n : ℕ, μ n * (f n : ℝ≥0∞) ^ p := by
  simp only [natMoment, PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro n
  simp [ite_mul]

private lemma nat_moment_bind (μ : PMF ℕ) (f : ℕ → PMF ℕ) (p : ℕ) :
    natMoment (μ.bind f) p = ∑' n : ℕ, μ n * natMoment (f n) p := by
  simp only [natMoment, PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]

private lemma entrance_moment_step (j p : ℕ) :
    natMoment (entranceLaw (j + 1)) p =
      ∑ i ∈ range (p + 1), (p.choose i : ℝ≥0∞) *
        natMoment (entranceLaw j) i * holdingMoment j (p - i) := by
  have hex (t w : ℕ) : ((t + w + 1 : ℕ) : ℝ≥0∞) ^ p =
      ∑ i ∈ range (p + 1), (t : ℝ≥0∞) ^ i *
        ((w + 1 : ℕ) : ℝ≥0∞) ^ (p - i) * (p.choose i : ℝ≥0∞) := by
    rw [show ((t + w + 1 : ℕ) : ℝ≥0∞) =
      (t : ℝ≥0∞) + ((w + 1 : ℕ) : ℝ≥0∞) by push_cast; exact add_assoc _ _ _]
    exact add_pow _ _ _
  rw [entranceLaw, nat_moment_bind]
  simp_rw [nat_moment_map, hex, mul_sum,
    Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply sum_congr rfl
  intro i hi
  unfold natMoment holdingMoment
  simp only [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro t
  apply tsum_congr
  intro w
  ac_rfl

def meanScale (j : ℕ) : ℝ≥0∞ := ∑ u ∈ range j, (2 : ℝ≥0∞) ^ (u + 1)

private lemma mean_scale_step (j : ℕ) :
    meanScale (j + 1) = meanScale j + (2 : ℝ≥0∞) ^ (j + 1) := by
  simp [meanScale, sum_range_succ]

private lemma entrance_moment_bound (j p : ℕ) :
    natMoment (entranceLaw j) p ≤ (p.factorial : ℝ≥0∞) * meanScale j ^ p := by
  induction j generalizing p with
  | zero =>
    cases p with
    | zero => simp [nat_moment_zero]
    | succ p => simp [entranceLaw, natMoment, PMF.pure_apply, meanScale]
  | succ j ih =>
    rw [entrance_moment_step, mean_scale_step]
    calc
      ∑ i ∈ range (p + 1), (p.choose i : ℝ≥0∞) *
          natMoment (entranceLaw j) i * holdingMoment j (p - i)
        ≤ ∑ i ∈ range (p + 1), (p.choose i : ℝ≥0∞) *
          ((i.factorial : ℝ≥0∞) * meanScale j ^ i) *
          (((p - i).factorial : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (j + 1)) ^ (p - i)) := by
            apply sum_le_sum
            intro i hi
            exact mul_le_mul' (mul_le_mul_right (ih i) _) (holding_moment_bound j (p - i))
      _ = (p.factorial : ℝ≥0∞) * ∑ i ∈ range (p + 1),
          meanScale j ^ i * ((2 : ℝ≥0∞) ^ (j + 1)) ^ (p - i) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro i hi
            have h : (p.choose i : ℝ≥0∞) * (i.factorial : ℝ≥0∞) *
                ((p - i).factorial : ℝ≥0∞) = (p.factorial : ℝ≥0∞) := by
              exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by simpa using hi : i ≤ p)
            calc
              _ = ((p.choose i : ℝ≥0∞) * (i.factorial : ℝ≥0∞) *
                ((p - i).factorial : ℝ≥0∞)) *
                (meanScale j ^ i * ((2 : ℝ≥0∞) ^ (j + 1)) ^ (p - i)) := by ac_rfl
              _ = _ := by rw [h]
      _ ≤ (p.factorial : ℝ≥0∞) *
          (meanScale j + (2 : ℝ≥0∞) ^ (j + 1)) ^ p := by
            apply mul_le_mul_right
            rw [add_pow]
            apply sum_le_sum
            intro i hi
            have hc : (1 : ℝ≥0∞) ≤ p.choose i := by
              exact_mod_cast Nat.choose_pos (by simpa using hi : i ≤ p)
            simpa only [mul_one] using
              mul_le_mul_right hc (meanScale j ^ i * ((2 : ℝ≥0∞) ^ (j + 1)) ^ (p - i))

private lemma mean_scale_bound (j : ℕ) : meanScale j ≤ (2 : ℝ≥0∞) ^ (j + 1) := by
  induction j with
  | zero => simp [meanScale]
  | succ j ih =>
    rw [mean_scale_step]
    calc
      meanScale j + (2 : ℝ≥0∞) ^ (j + 1) ≤
          (2 : ℝ≥0∞) ^ (j + 1) + (2 : ℝ≥0∞) ^ (j + 1) := by gcongr
      _ = _ := by simp only [pow_succ, mul_two]

def discountedWeight (m : ℕ) (s : ℝ) (k : ℕ) : ℝ≥0∞ :=
  if k = 0 then 0 else (k : ℝ≥0∞) ^ m * ENNReal.ofReal (Real.exp (-s * k))

private lemma discounted_weight_zero (m : ℕ) (s : ℝ) : discountedWeight m s 0 = 0 := by
  simp [discountedWeight]

private lemma discounted_weight_le (m : ℕ) (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    discountedWeight m s k ≤ (k : ℝ≥0∞) ^ m := by
  by_cases hk : k = 0
  · simp [discountedWeight, hk]
  · rw [discountedWeight, if_neg hk]
    have he : ENNReal.ofReal (Real.exp (-s * k)) ≤ 1 := by
      simpa using ENNReal.ofReal_le_ofReal
        (Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) k] : -s * (k : ℝ) ≤ 0))
    simpa using mul_le_mul_right he ((k : ℝ≥0∞) ^ m)

private lemma interval_exit_law (j : ℕ) :
    (intervalLaw j).map (fun tw => tw.1 + tw.2 + 1) = entranceLaw (j + 1) := by
  simp [intervalLaw, entranceLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]

private lemma interval_exit_moment (j p : ℕ) :
    (∫⁻ tw, ((tw.1 + tw.2 + 1 : ℕ) : ℝ≥0∞) ^ p ∂(intervalLaw j).toMeasure) =
      natMoment (entranceLaw (j + 1)) p := by
  calc
    _ = ∫⁻ n : ℕ, (n : ℝ≥0∞) ^ p ∂((intervalLaw j).toMeasure.map
        (fun tw => tw.1 + tw.2 + 1)) := by
      rw [lintegral_map (by fun_prop) (by fun_prop)]
    _ = _ := by
      rw [PMF.toMeasure_map _ _ (by fun_prop), interval_exit_law, lintegral_countable']
      simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
      unfold natMoment
      apply tsum_congr
      intro n
      exact mul_comm _ _

private lemma occupation_upper_moment (m j : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    actualOccupation (discountedWeight m s) j ≤ natMoment (entranceLaw (j + 1)) (m + 1) := by
  rw [actual_analytical_occupation _ (discounted_weight_zero m s), analyticalOccupation]
  calc
    _ ≤ ∫⁻ tw, ((tw.1 + tw.2 + 1 : ℕ) : ℝ≥0∞) ^ (m + 1)
        ∂(intervalLaw j).toMeasure := by
      apply lintegral_mono
      intro tw
      let U := tw.1 + tw.2 + 1
      calc
        _ ≤ ∑ _k ∈ Ico (max 1 tw.1) U, (U : ℝ≥0∞) ^ m := by
          apply sum_le_sum
          intro k hk
          apply (discounted_weight_le m s hs k).trans
          have hkU : k ≤ U := (mem_Ico.mp hk).2.le
          exact pow_le_pow_left' (by exact_mod_cast hkU) m
        _ = ((U - max 1 tw.1 : ℕ) : ℝ≥0∞) * (U : ℝ≥0∞) ^ m := by
          simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ (U : ℝ≥0∞) * (U : ℝ≥0∞) ^ m := by
          gcongr
          exact Nat.sub_le _ _
        _ = (U : ℝ≥0∞) ^ (m + 1) := by rw [pow_succ'];
    _ = _ := interval_exit_moment j (m + 1)

private lemma occupation_upper (m j : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    actualOccupation (discountedWeight m s) j ≤
      ((m + 1).factorial : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (j + 2)) ^ (m + 1) := by
  apply (occupation_upper_moment m j s hs).trans
  apply (entrance_moment_bound (j + 1) (m + 1)).trans
  gcongr
  exact mean_scale_bound (j + 1)

private lemma geometric_tail_lower_real (L : ℕ) (hL : 2 ≤ L) :
    Real.exp (-1) ≤ (1 - 1 / (L : ℝ)) ^ (L - 1) := by
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hN : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ L)]
    norm_num
  have hq : 0 < (1 - 1 / (L : ℝ)) := by
    rw [sub_pos, div_lt_one hLpos]
    linarith
  have hid : ((L - 1 : ℕ) : ℝ) * (1 - (1 - 1 / (L : ℝ))⁻¹) = -1 := by
    rw [hN]
    field_simp [hLpos.ne', (by linarith : (L : ℝ) - 1 ≠ 0)]
    <;> ring
  calc
    Real.exp (-1) = Real.exp (((L - 1 : ℕ) : ℝ) *
        (1 - (1 - 1 / (L : ℝ))⁻¹)) := congrArg Real.exp hid.symm
    _ ≤ Real.exp (((L - 1 : ℕ) : ℝ) * Real.log (1 - 1 / (L : ℝ))) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hq) (by positivity)
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hq]

private lemma holding_long_probability (j : ℕ) :
    ENNReal.ofReal (Real.exp (-1)) ≤
      (failures j).toMeasure (Set.Ici (2 ^ (j + 1) - 1)) := by
  rw [failures, Measure.toPMF_toMeasure,
    D5.S3.Analytic.PrimeProducts.GeometricResidualMemorylessness.geometric_tail_mass
      (parameter j) (parameter_ne_zero j)]
  have hp : (parameter j : ℝ) = 1 / ((2 ^ (j + 1) : ℕ) : ℝ) := by
    simp [parameter, success, one_div, inv_pow]
  rw [hp]
  apply ENNReal.ofReal_le_ofReal
  apply geometric_tail_lower_real
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

private lemma entrance_early_probability (j : ℕ) :
    (3 / 4 : ℝ≥0∞) ≤
      (entranceLaw j).toMeasure {t | t < 4 * 2 ^ (j + 1)} := by
  let μ := (entranceLaw j).toMeasure
  let L : ℝ≥0∞ := 2 ^ (j + 1)
  have hm : (∫⁻ t : ℕ, (t : ℝ≥0∞) ∂μ) ≤ L := by
    dsimp [μ]
    rw [lintegral_countable']
    simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    have hn := (entrance_moment_bound j 1).trans (by
      simpa using mean_scale_bound j)
    simpa [natMoment, pow_one, mul_comm] using hn
  have hL0 : L ≠ 0 := by simp [L]
  have hLt : L ≠ ⊤ := by simp [L]
  have ht := (meas_ge_le_lintegral_div (μ := μ)
    (f := fun t : ℕ => (t : ℝ≥0∞)) (measurable_of_countable _).aemeasurable
    (by simp [L] : 4 * L ≠ 0) (by finiteness : 4 * L ≠ ⊤)).trans
      (ENNReal.div_le_div_right hm (4 * L))
  have hdiv : L / (4 * L) = (1 / 4 : ℝ≥0∞) := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    calc
      L * ((4 : ℝ≥0∞)⁻¹ * L⁻¹) = (4 : ℝ≥0∞)⁻¹ * (L * L⁻¹) := by ac_rfl
      _ = _ := by rw [ENNReal.mul_inv_cancel hL0 hLt]; norm_num
  rw [hdiv] at ht
  have he : {t : ℕ | 4 * L ≤ (t : ℝ≥0∞)} =
      {t : ℕ | t < 4 * 2 ^ (j + 1)}ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    dsimp [L]
    norm_cast
  rw [he] at ht
  have ha := measure_add_measure_compl (μ := μ)
    (MeasurableSet.of_discrete (s := {t : ℕ | t < 4 * 2 ^ (j + 1)}))
  rw [measure_univ] at ha
  apply (ENNReal.add_le_add_iff_right (by norm_num : (1 / 4 : ℝ≥0∞) ≠ ⊤)).mp
  calc
    (3 / 4 : ℝ≥0∞) + 1 / 4 = 1 := by
      change (↑(3 : ℝ≥0) : ℝ≥0∞) / ↑(4 : ℝ≥0) +
        ↑(1 : ℝ≥0) / ↑(4 : ℝ≥0) = ↑(1 : ℝ≥0)
      rw [← ENNReal.coe_div (by norm_num), ← ENNReal.coe_div (by norm_num),
        ← ENNReal.coe_add]
      norm_num
    _ = _ := ha.symm
    _ ≤ _ := by gcongr

private lemma interval_rectangle_probability (j : ℕ) (A B : Set ℕ) :
    (intervalLaw j).toMeasure (A ×ˢ B) =
      (entranceLaw j).toMeasure A * (failures j).toMeasure B := by
  rw [intervalLaw, PMF.toMeasure_bind_apply _ _ _ MeasurableSet.of_discrete,
    PMF.toMeasure_apply _ MeasurableSet.of_discrete, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro t
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) MeasurableSet.of_discrete]
  by_cases ht : t ∈ A
  · have he : (fun w : ℕ => (t, w)) ⁻¹' (A ×ˢ B) = B := by ext w; simp [ht]
    simp [he, Set.indicator_of_mem ht]
  · have he : (fun w : ℕ => (t, w)) ⁻¹' (A ×ˢ B) = ∅ := by ext w; simp [ht]
    simp [he, Set.indicator_of_notMem ht]

private lemma good_interval_lower (m j t w : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hscale : s * (2 : ℝ) ^ (j + 1) ≤ 1)
    (ht : t < 4 * 2 ^ (j + 1)) (hw : 2 ^ (j + 1) - 1 ≤ w) :
    (2 : ℝ≥0∞) ^ (j * (m + 1)) * ENNReal.ofReal (Real.exp (-5)) ≤
      ∑ k ∈ Ico (max 1 t) (t + w + 1), discountedWeight m s k := by
  let H : ℕ := 2 ^ j
  let L : ℕ := 2 ^ (j + 1)
  have hL : L = H + H := by simp [L, H, pow_succ, mul_two]
  have hH : 1 ≤ H := Nat.one_le_pow _ _ (by norm_num)
  have hL0 : 1 ≤ L := by omega
  have hcard : #(Ico (t + H) (t + L)) = H := by rw [Nat.card_Ico]; omega
  have hsub : Ico (t + H) (t + L) ⊆ Ico (max 1 t) (t + w + 1) := by
    intro k hk
    simp only [mem_Ico] at hk ⊢
    dsimp [L] at *
    omega
  have hterm (k : ℕ) (hk : k ∈ Ico (t + H) (t + L)) :
      (H : ℝ≥0∞) ^ m * ENNReal.ofReal (Real.exp (-5)) ≤ discountedWeight m s k := by
    have hk0 : k ≠ 0 := by have := mem_Ico.mp hk; omega
    have hkH : H ≤ k := by have := mem_Ico.mp hk; omega
    have hkL : (k : ℝ) ≤ 5 * (2 : ℝ) ^ (j + 1) := by
      have : k ≤ 5 * L := by have := mem_Ico.mp hk; omega
      exact_mod_cast this
    rw [discountedWeight, if_neg hk0]
    apply mul_le_mul'
    · exact pow_le_pow_left' (by exact_mod_cast hkH) m
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hkL hs
      nlinarith
  calc
    _ = (H : ℝ≥0∞) ^ (m + 1) * ENNReal.ofReal (Real.exp (-5)) := by
      simp [H, Nat.cast_pow, pow_mul]
    _ = ∑ _k ∈ Ico (t + H) (t + L),
        (H : ℝ≥0∞) ^ m * ENNReal.ofReal (Real.exp (-5)) := by
      simp [sum_const, hcard, nsmul_eq_mul, pow_succ']
      ac_rfl
    _ ≤ ∑ k ∈ Ico (t + H) (t + L), discountedWeight m s k := sum_le_sum hterm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le)

private lemma occupation_lower_dyadic (m j : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hscale : s * (2 : ℝ) ^ (j + 1) ≤ 1) :
    (3 / 4 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-6)) *
      (2 : ℝ≥0∞) ^ (j * (m + 1)) ≤ actualOccupation (discountedWeight m s) j := by
  let A : Set ℕ := {t | t < 4 * 2 ^ (j + 1)}
  let B : Set ℕ := Set.Ici (2 ^ (j + 1) - 1)
  let C := (2 : ℝ≥0∞) ^ (j * (m + 1)) * ENNReal.ofReal (Real.exp (-5))
  have hevent : (3 / 4 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-1)) ≤
      (intervalLaw j).toMeasure (A ×ˢ B) := by
    rw [interval_rectangle_probability]
    exact mul_le_mul' (entrance_early_probability j) (holding_long_probability j)
  have hpoint : C * (intervalLaw j).toMeasure (A ×ˢ B) ≤
      analyticalOccupation (discountedWeight m s) j := by
    calc
      _ = ∫⁻ tw, (A ×ˢ B).indicator (fun _ => C) tw ∂(intervalLaw j).toMeasure := by
        rw [lintegral_indicator MeasurableSet.of_discrete, setLIntegral_const]
      _ ≤ _ := by
        unfold analyticalOccupation
        apply lintegral_mono
        intro tw
        by_cases ht : tw ∈ A ×ˢ B
        · rw [Set.indicator_of_mem ht]
          exact good_interval_lower m j tw.1 tw.2 s hs hscale ht.1 ht.2
        · rw [Set.indicator_of_notMem ht]
          exact zero_le
  rw [actual_analytical_occupation _ (discounted_weight_zero m s)]
  apply le_trans _ hpoint
  calc
    _ = C * ((3 / 4 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-1))) := by
      dsimp [C]
      rw [show (-6 : ℝ) = -5 + -1 by norm_num, Real.exp_add,
        ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
    _ ≤ _ := mul_le_mul_right hevent C

def lowerConstant (m : ℕ) : ℝ := 3 * Real.exp (-6) / 2 ^ (m + 3)

def upperConstant (m : ℕ) : ℝ := Real.exp 1 * (m + 1).factorial * 2 ^ (m + 1)

/-- Source phases use indices j≥1, while the row carrier begins at zero. -/
def occupation (m : ℕ) (s : ℝ) (j : ℕ) : ℝ :=
  (actualOccupation (discountedWeight m s) (j - 1)).toReal

private lemma occupation_bounds (m n : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hscale : s * (2 : ℝ) ^ (n + 1) ≤ 1) :
    lowerConstant m * (2 : ℝ) ^ ((n + 1) * (m + 1)) ≤ occupation m s (n + 1) ∧
      occupation m s (n + 1) ≤ upperConstant m * (2 : ℝ) ^ ((n + 1) * (m + 1)) := by
  have hu := occupation_upper m n s hs
  have hf : actualOccupation (discountedWeight m s) n ≠ ⊤ :=
    (lt_of_le_of_lt hu (by finiteness)).ne
  have hl := ENNReal.toReal_mono hf (occupation_lower_dyadic m n s hs hscale)
  have hur := ENNReal.toReal_mono (by finiteness) hu
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hl hur
  have hden : (2 : ℝ) ^ (m + 3) = (2 : ℝ) ^ (m + 1) * 4 := by
    rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
    norm_num
  have hnum : (2 : ℝ) ^ ((n + 1) * (m + 1)) =
      (2 : ℝ) ^ (n * (m + 1)) * (2 : ℝ) ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    ring
  have hlow : lowerConstant m * (2 : ℝ) ^ ((n + 1) * (m + 1)) =
      3 / 4 * Real.exp (-6) * (2 : ℝ) ^ (n * (m + 1)) := by
    rw [lowerConstant, hden, hnum]
    field_simp
  have hupp : ((2 : ℝ) ^ (n + 2)) ^ (m + 1) =
      (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ ((n + 1) * (m + 1)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  constructor
  · simpa [occupation, hlow] using hl
  · have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    apply le_trans (by simpa [occupation, hupp] using hur)
    unfold upperConstant
    have hnon : 0 ≤ ((m + 1).factorial : ℝ) *
        (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ ((n + 1) * (m + 1)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right he hnon]

/-- Uniform discounted actual phase occupations, with every finite cap. -/
theorem uniform_discounted_phase_occupation (m j : ℕ) (hj : 1 ≤ j)
    (s eta : ℝ) (hs : 0 < s) (hscale : s * (2 : ℝ) ^ j ≤ eta) (heta : eta ≤ 1) :
    0 < lowerConstant m ∧ 0 < upperConstant m ∧
    entranceLaw 0 = PMF.pure 0 ∧
    actualOccupation (discountedWeight m s) (j - 1) ≠ ⊤ ∧
    actualOccupation (discountedWeight m s) (j - 1) =
      analyticalOccupation (discountedWeight m s) (j - 1) ∧
    lowerConstant m * (2 : ℝ) ^ (j * (m + 1)) ≤ occupation m s j ∧
    occupation m s j ≤ upperConstant m * (2 : ℝ) ^ (j * (m + 1)) ∧
    (∀ (J : ℕ) (hJ : j ≤ J),
      (∑' k : ℕ, discountedWeight m s k *
        finiteCappedLaw J k ⟨j - 1, by omega⟩) =
      actualOccupation (discountedWeight m s) (j - 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hb := occupation_bounds m n s hs.le (hscale.trans heta)
  have hf : actualOccupation (discountedWeight m s) n ≠ ⊤ :=
    (lt_of_le_of_lt (occupation_upper m n s hs.le) (by finiteness)).ne
  refine ⟨by unfold lowerConstant; positivity, by unfold upperConstant; positivity,
    rfl, hf, actual_analytical_occupation _ (discounted_weight_zero m s) _, hb.1, hb.2, ?_⟩
  intro J hJ
  exact finite_capped_live_occupation _ J n (by omega)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.GeometricPhaseOccupation
