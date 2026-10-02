/- GID: D5/S3/Observer/ProbabilisticClosure/BeneficialMarkerDeflection
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/BeneficialMarkerDeflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Support detects an actual pulse improving true marker-stopping expectation. -/

import D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ProbabilisticClosure.BeneficialMarkerDeflection

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkovPrefixMass

/-- Preserve infinity when embedding the actual first-hit query count. -/
def tauENN (t : WithTop ℕ) : ℝ≥0∞ := WithTop.recTopCoe (⊤ : ℝ≥0∞) (fun n : ℕ => (n : ℝ≥0∞)) t


local instance : MeasurableSpace (List Bool) := ⊤

/-- One shared parameter draw followed by the existing independent-seed joint law. -/
noncomputable def priorLaw {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed)
    (alpha : unitInterval) (μ : Measure unitInterval) : Measure (Seed × Source) :=
  μ.bind (jointLaw ν alpha)

/-- True extended stopping expectation under the actual mixed source law. -/
noncomputable def expectedCost {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (ν : Measure Seed) (alpha : unitInterval) (μ : Measure unitInterval) : ℝ≥0∞ :=
  ∫⁻ p, tauENN (stoppingTime policy p.1 p.2) ∂priorLaw ν alpha μ


noncomputable def replayWeight {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (ν : Measure Seed) (q : unitInterval) : ℝ :=
  (1 - (q : ℝ)) * ∑' n : ℕ, lambda policy ν (n + 1) * (q : ℝ) ^ n

noncomputable def reciprocalMoment (μ : Measure unitInterval) : ℝ≥0∞ :=
  ∫⁻ q, (ENNReal.ofReal (1 - (q : ℝ)))⁻¹ ∂μ

noncomputable def coefficient (alpha : unitInterval) (μ : Measure unitInterval) (m : ℕ) : ℝ :=
  ∫ q, (1 - (q : ℝ)) * ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ (m - 1) ∂μ


noncomputable def gap (μ : Measure unitInterval) (n : ℕ) : ℝ :=
  ∫ q, (1 - (q : ℝ)) * (q : ℝ) ^ n ∂μ


noncomputable def firstNegative (alpha : unitInterval) (μ : Measure unitInterval) : WithTop ℕ :=
  sInf ((fun m : ℕ => (m : WithTop ℕ)) '' {m | 1 ≤ m ∧ coefficient alpha μ m < 0})

/-- Query right only at the two acquired-history indices 2N and 2N+1. -/
def pulse {Seed : Type*} [MeasurableSpace Seed] (N : ℕ) : Policy Seed where
  choose := fun _ actions _ => decide (actions.length + 1 = 2 * N ∨ actions.length + 1 = 2 * N + 1)
  measurable_section := fun _ _ => measurable_const

def alwaysLeft {Seed : Type*} [MeasurableSpace Seed] : Policy Seed where
  choose := fun _ _ _ => false
  measurable_section := fun _ _ => measurable_const

universe u
set_option maxHeartbeats 2400000 in
-- The joint proof elaborates seed measurability, true tail integration, and the support limit.

/-- The full beneficial-deflection support criterion and its true-cost boundaries. -/
theorem beneficial_marker_deflection (alpha : unitInterval)
    (ha : 0 < (alpha : ℝ) ∧ (alpha : ℝ) < 1)
    (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (hQ : ∀ᵐ (q : unitInterval) ∂μ, 0 < (q : ℝ) ∧ (q : ℝ) < 1) :
    (firstNegative alpha μ < ⊤ ↔
      (alpha : ℝ) / (1 - (alpha : ℝ)) < essSup (fun q : unitInterval => (q : ℝ)) μ) ∧
    (Summable (fun n : ℕ => |coefficient alpha μ (n + 1)|) ∧
      (∑' n : ℕ, |coefficient alpha μ (n + 1)|) < 1 ∧
      (∀ {Seed : Type u} [MeasurableSpace Seed] (policy : Policy Seed)
        (ν : Measure Seed) [IsProbabilityMeasure ν],
        Summable (fun n : ℕ => lambda policy ν (n + 1) * coefficient alpha μ (n + 1)))) ∧
    (∀ {Seed : Type u} [MeasurableSpace Seed] (policy : Policy Seed)
      (ν : Measure Seed) [IsProbabilityMeasure ν],
      ENNReal.ofReal (alpha : ℝ) * reciprocalMoment μ ≤ expectedCost policy ν alpha μ ∧
      expectedCost policy ν alpha μ ≤ 1 + 2 * reciprocalMoment μ ∧
      (expectedCost policy ν alpha μ ≠ ⊤ ↔ reciprocalMoment μ ≠ ⊤) ∧
      (reciprocalMoment μ ≠ ⊤ → (expectedCost policy ν alpha μ).toReal =
        2 * (reciprocalMoment μ).toReal - (1 - (alpha : ℝ)) +
        ∑' n : ℕ, lambda policy ν (n + 1) * coefficient alpha μ (n + 1))) ∧
    (∀ {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν],
      reciprocalMoment μ ≠ ⊤ →
      (expectedCost (alwaysLeft : Policy Seed) ν alpha μ).toReal =
        2 * (reciprocalMoment μ).toReal - (1 - (alpha : ℝ))) ∧
    (∀ {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν],
      reciprocalMoment μ ≠ ⊤ →
      ((∃ policy : Policy Seed,
        expectedCost policy ν alpha μ < expectedCost alwaysLeft ν alpha μ) ↔
        (alpha : ℝ) / (1 - (alpha : ℝ)) < essSup (fun q : unitInterval => (q : ℝ)) μ)) ∧
    ((1 / 2 : ℝ) ≤ (alpha : ℝ) →
      (∀ m, 1 ≤ m → 0 < coefficient alpha μ m) ∧ firstNegative alpha μ = ⊤ ∧
      (∀ {Seed : Type u} [MeasurableSpace Seed] (policy : Policy Seed)
        (ν : Measure Seed) [IsProbabilityMeasure ν], reciprocalMoment μ ≠ ⊤ →
        expectedCost alwaysLeft ν alpha μ ≤ expectedCost policy ν alpha μ)) ∧
    (∀ {Seed Seed' : Type u} [MeasurableSpace Seed] [MeasurableSpace Seed']
      (policy : Policy Seed) (policy' : Policy Seed')
      (ν : Measure Seed) (ν' : Measure Seed') [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'],
      expectedCost policy ν alpha μ ≠ ⊤ → expectedCost policy' ν' alpha μ ≠ ⊤ →
      |(expectedCost policy ν alpha μ).toReal - (expectedCost policy' ν' alpha μ).toReal| < 1) ∧
    (reciprocalMoment μ = ⊤ →
      ∀ {Seed : Type u} [MeasurableSpace Seed] (policy : Policy Seed)
        (ν : Measure Seed) [IsProbabilityMeasure ν],
        expectedCost policy ν alpha μ = ⊤ ∧
        ¬ expectedCost policy ν alpha μ < expectedCost alwaysLeft ν alpha μ) := by
  classical
  have hcorrections :
    Summable (fun n : ℕ => |coefficient alpha μ (n + 1)|) ∧
      (∑' n : ℕ, |coefficient alpha μ (n + 1)|) < 1 ∧
      (∀ l : ℕ → ℝ, (∀ n, 0 ≤ l n ∧ l n ≤ 1) →
        HasSum (fun n : ℕ => l n * coefficient alpha μ (n + 1))
          (∫ q : unitInterval, ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) *
            (1 - (q : ℝ)) * (∑' n : ℕ, l n * (q : ℝ) ^ n) ∂μ)) := by
    let δ : unitInterval → ℝ := fun q => (alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)
    let B (n : ℕ) (q : unitInterval) : ℝ := (1 - (q : ℝ)) * |δ q| * (q : ℝ) ^ n
    let F (n : ℕ) (q : unitInterval) : ℝ := (1 - (q : ℝ)) * δ q * (q : ℝ) ^ n
    let C : ℝ := max (alpha : ℝ) (1 - (alpha : ℝ))
    have hδ (q : unitInterval) : |δ q| ≤ C := by
      have hq0 := unitInterval.nonneg q
      have hq1 := unitInterval.le_one q
      have hC0 := le_max_left (alpha : ℝ) (1 - (alpha : ℝ))
      have hC1 := le_max_right (alpha : ℝ) (1 - (alpha : ℝ))
      apply abs_le.mpr
      dsimp [δ]
      constructor <;> nlinarith
    have hC : C < 1 := max_lt ha.2 (by linarith [ha.1])
    have hiδ : Integrable (fun q => |δ q|) μ :=
      (integrable_const C).mono' (by fun_prop) (Eventually.of_forall fun q => by
        simpa only [Real.norm_eq_abs, abs_abs] using hδ q)
    have hbs (q : unitInterval) (hq : (q : ℝ) < 1) :
        HasSum (fun n : ℕ => B n q) |δ q| := by
      have h := (hasSum_geometric_of_lt_one (unitInterval.nonneg q) hq).mul_left
        ((1 - (q : ℝ)) * |δ q|)
      have hx := sub_pos.mpr hq
      have he : ((1 - (q : ℝ)) * |δ q|) * (1 - (q : ℝ))⁻¹ = |δ q| := by
        rw [mul_right_comm, mul_inv_cancel₀ hx.ne', one_mul]
      simpa only [he] using h
    have hBint : Integrable (fun q => ∑' n : ℕ, B n q) μ := by
      apply hiδ.congr
      filter_upwards [hQ] with q hq
      exact (hbs q hq.2).tsum_eq.symm
    have hnorm (n : ℕ) (q : unitInterval) : ‖F n q‖ = B n q := by
      simp [F, B, Real.norm_eq_abs, abs_of_nonneg (unitInterval.one_minus_nonneg q),
        abs_of_nonneg (unitInterval.nonneg q)]
    have hsumNorm : HasSum (fun n : ℕ => ∫ q, B n q ∂μ) (∫ q, |δ q| ∂μ) := by
      apply hasSum_integral_of_dominated_convergence B
      · intro n
        fun_prop
      · intro n
        exact Eventually.of_forall (fun q => by
          rw [Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (mul_nonneg (unitInterval.one_minus_nonneg q) (abs_nonneg _))
              (pow_nonneg (unitInterval.nonneg q) n))])
      · exact hQ.mono (fun q hq => (hbs q hq.2).summable)
      · exact hBint
      · exact hQ.mono (fun q hq => hbs q hq.2)
    have hvint (n : ℕ) : Integrable (F n) μ := by
      apply (integrable_const C).mono' (by fun_prop)
      apply Eventually.of_forall
      intro q
      rw [hnorm]
      have hp : (q : ℝ) ^ n ≤ 1 := pow_le_one₀ (unitInterval.nonneg q) (unitInterval.le_one q)
      dsimp [B]
      calc
        _ ≤ |δ q| * 1 := mul_le_mul
          (mul_le_of_le_one_left (abs_nonneg _) (unitInterval.one_minus_le_one q)) hp
          (pow_nonneg (unitInterval.nonneg q) n) (abs_nonneg _)
        _ = |δ q| := by ring
        _ ≤ C := hδ q
    have hvbound (n : ℕ) : |coefficient alpha μ (n + 1)| ≤ ∫ q, B n q ∂μ := by
      have h := norm_integral_le_integral_norm (F n) (μ := μ)
      simp only [Real.norm_eq_abs, hnorm] at h
      simpa [coefficient, F, δ] using h
    have hs : Summable (fun n : ℕ => |coefficient alpha μ (n + 1)|) :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hvbound hsumNorm.summable
    have hlt : (∑' n : ℕ, |coefficient alpha μ (n + 1)|) < 1 := by
      calc
        _ ≤ ∑' n : ℕ, ∫ q, B n q ∂μ := hs.tsum_le_tsum hvbound hsumNorm.summable
        _ = ∫ q, |δ q| ∂μ := hsumNorm.tsum_eq
        _ ≤ C := by
          simpa using integral_mono_ae hiδ (integrable_const C) (Eventually.of_forall hδ)
        _ < 1 := hC
    refine ⟨hs, hlt, ?_⟩
    intro l hl
    have hlim (q : unitInterval) (hq : (q : ℝ) < 1) :
        HasSum (fun n : ℕ => l n * F n q)
          (δ q * (1 - (q : ℝ)) * (∑' n : ℕ, l n * (q : ℝ) ^ n)) := by
      have hw : Summable (fun n : ℕ => l n * (q : ℝ) ^ n) :=
        Summable.of_nonneg_of_le
          (fun n => mul_nonneg (hl n).1 (pow_nonneg (unitInterval.nonneg q) _))
          (fun n => mul_le_of_le_one_left (pow_nonneg (unitInterval.nonneg q) _) (hl n).2)
          (summable_geometric_of_lt_one (unitInterval.nonneg q) hq)
      have he : (fun n : ℕ => l n * F n q) =
          (fun n : ℕ => (δ q * (1 - (q : ℝ))) * (l n * (q : ℝ) ^ n)) := by
        funext n
        dsimp [F]
        ring
      rw [he]
      exact hw.hasSum.mul_left _
    have hweighted : HasSum (fun n : ℕ => ∫ q, l n * F n q ∂μ)
        (∫ q : unitInterval, δ q * (1 - (q : ℝ)) * (∑' n : ℕ, l n * (q : ℝ) ^ n) ∂μ) := by
      apply hasSum_integral_of_dominated_convergence B
      · intro n
        fun_prop
      · intro n
        apply Eventually.of_forall
        intro q
        rw [norm_mul, hnorm]
        have hb0 : 0 ≤ B n q := mul_nonneg
          (mul_nonneg (unitInterval.one_minus_nonneg q) (abs_nonneg _))
          (pow_nonneg (unitInterval.nonneg q) n)
        apply mul_le_of_le_one_left hb0
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hl n).1] using (hl n).2
      · exact hQ.mono (fun q hq => (hbs q hq.2).summable)
      · exact hBint
      · exact hQ.mono (fun q hq => hlim q hq.2)
    have he (n : ℕ) : (∫ q, l n * F n q ∂μ) = l n * coefficient alpha μ (n + 1) := by
      rw [integral_const_mul]
      simp only [F, δ, coefficient, Nat.add_sub_cancel]
    simpa only [he, δ] using hweighted
  have hsupport :
    (firstNegative alpha μ < ⊤ ↔
      (alpha : ℝ) / (1 - (alpha : ℝ)) < essSup (fun q : unitInterval => (q : ℝ)) μ) ∧
    ((1 / 2 : ℝ) ≤ (alpha : ℝ) → ∀ m, 1 ≤ m → 0 < coefficient alpha μ m) := by
    have hratio : Tendsto (fun n : ℕ => gap μ (n + 1) / gap μ n) atTop
        (𝓝 (essSup (fun q : unitInterval => (q : ℝ)) μ)) := by
      let r := essSup (fun q : unitInterval => (q : ℝ)) μ
      let f : unitInterval → ℝ≥0∞ := fun q => ENNReal.ofReal (1 - (q : ℝ))
      have hf : Measurable f := by fun_prop
      let ξ := μ.withDensity f
      have hfinite : ∫⁻ q, f q ∂μ ≠ ⊤ := by
        have hle : ∫⁻ q, f q ∂μ ≤ 1 := by
          calc
            _ ≤ ∫⁻ q : unitInterval, (1 : ℝ≥0∞) ∂μ := by
              apply lintegral_mono
              intro q
              exact ENNReal.ofReal_le_one.mpr (by have := unitInterval.nonneg q; linarith)
            _ = 1 := by simp
        exact ne_of_lt (hle.trans_lt (by simp))
      let : IsFiniteMeasure ξ := isFiniteMeasure_withDensity hfinite
      have hae : ae ξ = ae μ := by
        apply Filter.ext
        intro s
        change (∀ᵐ (q : unitInterval) ∂ξ, q ∈ s) ↔ ∀ᵐ (q : unitInterval) ∂μ, q ∈ s
        rw [ae_withDensity_iff hf]
        constructor
        · intro h
          filter_upwards [h, hQ] with q hq hQq
          exact hq (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hQq.2)))
        · exact fun h => h.mono (fun q hq _ => hq)
      have hco : IsCoboundedUnder (· ≤ ·) (ae μ) (fun q : unitInterval => (q : ℝ)) :=
        isCoboundedUnder_le_of_le (ae μ) unitInterval.nonneg
      have hb : IsBoundedUnder (· ≤ ·) (ae μ) (fun q : unitInterval => (q : ℝ)) :=
        by
          refine ⟨1, ?_⟩
          change ∀ᵐ (q : unitInterval) ∂μ, (q : ℝ) ≤ 1
          exact Eventually.of_forall unitInterval.le_one
      have hu : ∀ᵐ (q : unitInterval) ∂μ, (q : ℝ) ≤ r := ae_le_essSup hb
      have hr : 0 < r := by
        obtain ⟨q, hq, hqr⟩ := (hQ.and hu).exists
        exact hq.1.trans_le hqr
      have hr1 : r ≤ 1 := essSup_le_of_ae_le 1 (Eventually.of_forall unitInterval.le_one) hco
      have huξ : ∀ᵐ (q : unitInterval) ∂ξ, (q : ℝ) ≤ r := by rw [hae]; exact hu
      have htail (d : ℝ) (hd : d < r) : 0 < ξ {q : unitInterval | d < (q : ℝ)} := by
        by_contra h
        have hz : ξ {q : unitInterval | d < (q : ℝ)} = 0 := le_antisymm (le_of_not_gt h) bot_le
        have hdμ : ∀ᵐ (q : unitInterval) ∂μ, (q : ℝ) ≤ d := by
          rw [← hae]
          simpa only [ae_iff, not_le] using hz
        exact hd.not_ge (essSup_le_of_ae_le d hdμ hco)
      let ζ : Measure ℝ := ξ.map (fun q : unitInterval => (q : ℝ))
      let : IsFiniteMeasure ζ := inferInstance
      have hsupp : ∀ᵐ x ∂ζ, x ∈ Icc 0 r := by
        apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
        exact huξ.mono (fun q hq => ⟨unitInterval.nonneg q, hq⟩)
      have hζ (u : Set ℝ) (hU : IsOpen u) (hru : r ∈ u) : 0 < ζ (u ∩ Icc 0 r) := by
        obtain ⟨l, t, hrt, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hru)
        have hlr : max l 0 < r := max_lt hrt.1 hr
        have ht := htail (max l 0) hlr
        rw [Measure.map_apply (by fun_prop) (hU.measurableSet.inter measurableSet_Icc)]
        apply ht.trans_le
        apply measure_mono_ae
        filter_upwards [huξ] with q hqr
        intro hq
        exact ⟨hsub ⟨(le_max_left l 0).trans_lt hq, hqr.trans_lt hrt.2⟩,
          unitInterval.nonneg q, hqr⟩
      have hpeak :=
        tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos
        (μ := ζ) (c := fun x : ℝ => x) (s := Icc 0 r) (x₀ := r) (g := fun x : ℝ => x)
        isCompact_Icc hζ continuous_id.continuousOn
        (fun y hy hne => lt_of_le_of_ne hy.2 hne)
        (fun x hx => hx.1) hr ⟨hr.le, le_rfl⟩
        (continuous_id.continuousOn.integrableOn_compact isCompact_Icc)
        continuous_id.continuousWithinAt
      have hg (n : ℕ) : ∫ x in Icc 0 r, x ^ n ∂ζ = gap μ n := by
        rw [Measure.restrict_eq_self_of_ae_mem hsupp]
        rw [integral_map (by fun_prop) (by fun_prop)]
        rw [integral_withDensity_eq_integral_toReal_smul hf]
        · simp [gap, f, smul_eq_mul, ENNReal.toReal_ofReal (unitInterval.one_minus_nonneg _)]
        · exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
      simpa only [smul_eq_mul, ← pow_succ, hg, div_eq_inv_mul, r] using hpeak
    let r := essSup (fun q : unitInterval => (q : ℝ)) μ
    have hi (n : ℕ) : Integrable (fun q : unitInterval => (1 - (q : ℝ)) * (q : ℝ) ^ n) μ := by
      apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
      apply Eventually.of_forall
      intro q
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (unitInterval.one_minus_nonneg q)
        (pow_nonneg (unitInterval.nonneg q) n))]
      exact mul_le_one₀ (unitInterval.one_minus_le_one q) (pow_nonneg (unitInterval.nonneg q) n)
        (pow_le_one₀ (n := n) (unitInterval.nonneg q) (unitInterval.le_one q))
    have hpos {f : unitInterval → ℝ} (hfi : Integrable f μ) (hp : ∀ᵐ q ∂μ, 0 < f q) :
        0 < ∫ q, f q ∂μ := by
      apply (integral_pos_iff_support_of_nonneg_ae (hp.mono (fun _ h => h.le)) hfi).mpr
      apply pos_iff_ne_zero.mpr
      intro hz
      have hzAE : ∀ᵐ q ∂μ, f q = 0 := by
        simpa only [ae_iff, Function.support, Set.mem_ofPred_eq, not_not] using hz
      obtain ⟨q, hpq, hzq⟩ := (hp.and hzAE).exists
      exact hpq.ne' hzq
    have hgpos (n : ℕ) : 0 < gap μ n := hpos (hi n)
      (hQ.mono (fun q hq => mul_pos (sub_pos.mpr hq.2) (pow_pos hq.1 n)))
    have hv (n : ℕ) : coefficient alpha μ (n + 1) =
        (alpha : ℝ) * gap μ n - (1 - (alpha : ℝ)) * gap μ (n + 1) := by
      unfold coefficient gap
      simp only [Nat.add_sub_cancel]
      have he : (fun q : unitInterval =>
          (1 - (q : ℝ)) * ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ n) =
          (fun q : unitInterval => (alpha : ℝ) * ((1 - (q : ℝ)) * (q : ℝ) ^ n) -
            (1 - (alpha : ℝ)) * ((1 - (q : ℝ)) * (q : ℝ) ^ (n + 1))) := by
        funext q
        rw [pow_succ]
        ring
      rw [he, integral_sub ((hi n).const_mul _) ((hi (n + 1)).const_mul _),
        integral_const_mul, integral_const_mul]
    have hco : IsCoboundedUnder (· ≤ ·) (ae μ) (fun q : unitInterval => (q : ℝ)) :=
      isCoboundedUnder_le_of_le (ae μ) unitInterval.nonneg
    have hb : IsBoundedUnder (· ≤ ·) (ae μ) (fun q : unitInterval => (q : ℝ)) := by
      refine ⟨1, ?_⟩
      change ∀ᵐ (q : unitInterval) ∂μ, (q : ℝ) ≤ 1
      exact Eventually.of_forall unitInterval.le_one
    have hupper : ∀ᵐ (q : unitInterval) ∂μ, (q : ℝ) ≤ r := ae_le_essSup hb
    have hgbound (n : ℕ) : gap μ (n + 1) / gap μ n ≤ r := by
      apply (div_le_iff₀ (hgpos n)).mpr
      unfold gap
      rw [← integral_const_mul]
      apply integral_mono_ae (hi (n + 1)) ((hi n).const_mul r)
      filter_upwards [hupper] with q hqr
      rw [pow_succ]
      have hf0 := mul_nonneg (unitInterval.one_minus_nonneg q)
        (pow_nonneg (unitInterval.nonneg q) n)
      nlinarith
    have halpha : 0 < 1 - (alpha : ℝ) := sub_pos.mpr ha.2
    have hcrit : (∃ n : ℕ, coefficient alpha μ (n + 1) < 0) ↔
        (alpha : ℝ) / (1 - (alpha : ℝ)) < r := by
      constructor
      · rintro ⟨n, hn⟩
        rw [hv] at hn
        have hgb := (div_le_iff₀ (hgpos n)).mp (hgbound n)
        apply (div_lt_iff₀ halpha).mpr
        nlinarith [hgpos n]
      · intro hr
        obtain ⟨n, hn⟩ := (hratio.eventually (eventually_gt_nhds hr)).exists
        refine ⟨n, ?_⟩
        rw [hv]
        have hgt := (div_lt_div_iff₀ halpha (hgpos n)).mp hn
        nlinarith
    constructor
    · rw [firstNegative, sInf_lt_iff]
      constructor
      · rintro ⟨k, ⟨m, hm, rfl⟩, hk⟩
        obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 1 := Nat.exists_eq_succ_of_ne_zero (by
          have hmn := hm.1
          omega)
        exact hcrit.mp ⟨n, hm.2⟩
      · intro hr
        obtain ⟨n, hn⟩ := hcrit.mpr hr
        exact ⟨((n + 1 : ℕ) : WithTop ℕ), ⟨n + 1, ⟨by omega, hn⟩, rfl⟩, by simp⟩
    · intro hhalf m hm
      obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      have hfi : Integrable (fun q : unitInterval =>
          (1 - (q : ℝ)) * ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ n) μ := by
        have he : (fun q : unitInterval =>
            (1 - (q : ℝ)) * ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ n) =
            (fun q : unitInterval => (alpha : ℝ) * ((1 - (q : ℝ)) * (q : ℝ) ^ n) -
              (1 - (alpha : ℝ)) * ((1 - (q : ℝ)) * (q : ℝ) ^ (n + 1))) := by
          funext q
          rw [pow_succ]
          ring
        rw [he]
        exact ((hi n).const_mul _).sub ((hi (n + 1)).const_mul _)
      change 0 < ∫ q, (1 - (q : ℝ)) * ((alpha : ℝ) -
        (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ n ∂μ
      apply hpos hfi
      filter_upwards [hQ] with q hq
      have hd : 0 < (alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ) := by nlinarith
      exact mul_pos (mul_pos (sub_pos.mpr hq.2) hd) (pow_pos hq.1 n)
  have hall {Seed : Type u} [MeasurableSpace Seed] (policy : Policy Seed)
      (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ENNReal.ofReal (alpha : ℝ) * reciprocalMoment μ ≤ expectedCost policy ν alpha μ ∧
    expectedCost policy ν alpha μ ≤ 1 + 2 * reciprocalMoment μ ∧
    (expectedCost policy ν alpha μ ≠ ⊤ ↔ reciprocalMoment μ ≠ ⊤) ∧
    (reciprocalMoment μ ≠ ⊤ →
      (expectedCost policy ν alpha μ).toReal =
        2 * (reciprocalMoment μ).toReal - (1 - (alpha : ℝ)) +
        ∑' n : ℕ, lambda policy ν (n + 1) * coefficient alpha μ (n + 1)) := by
    have hbridge : IsProbabilityMeasure (priorLaw ν alpha μ) ∧
        priorLaw ν alpha μ = ν.prod (μ.bind (sourceLaw alpha)) ∧
        expectedCost policy ν alpha μ =
          ∫⁻ q, ∑' n : ℕ, jointLaw ν alpha q
            {p | (n : WithTop ℕ) < stoppingTime policy p.1 p.2} ∂μ := by
      have hsource : Measurable (sourceLaw alpha) := by
        have harm (root : Bool) : Measurable (fun q : unitInterval => armLaw q root) := by
          classical
          have ht (x y : Bool) : Measurable (fun q : unitInterval => transition q x {y}) := by
            cases x <;> cases y <;>
              simp only [transition, bernoulliMeasure_def, Kernel.boolKernel_apply,
              Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Measure.coe_add,
              Measure.coe_smul, Pi.add_apply, Pi.smul_apply, MeasurableSpace.measurableSet_top,
              Measure.dirac_apply', Set.mem_singleton_iff, not_false_eq_true,
              Set.indicator_of_notMem, smul_zero, Set.indicator_of_mem, Pi.one_apply,
              ENNReal.smul_one, zero_add, add_zero, measurable_coe_nnreal_ennreal_iff,
              measurable_const] <;> fun_prop
          have hp (n : ℕ) (w : Fin (n + 1) → Bool) :
              Measurable (fun q : unitInterval =>
                (armLaw q root).map (fun x (i : Fin (n + 1)) => x i.val) {w}) := by
            have he (q : unitInterval) :=
              markov_chain_law_map_prefix_apply_singleton
                (Measure.dirac root) (transition q) n w
            simp only [armLaw] at *
            simp_rw [he]
            exact measurable_const.mul (Finset.measurable_fun_prod _ (fun i _ => ht _ _))
          have hprefix (n : ℕ) (S : Set (Fin (n + 1) → Bool)) :
              Measurable (fun q : unitInterval =>
                (armLaw q root).map (fun x (i : Fin (n + 1)) => x i.val) S) := by
            let F : Finset (Fin (n + 1) → Bool) := S.toFinite.toFinset
            have he : (F : Set (Fin (n + 1) → Bool)) = S := by simp [F]
            simp_rw [← he, ← sum_measure_singleton]
            exact Finset.measurable_fun_sum _ (fun w _ => hp n w)
          apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
            generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
          intro s hs
          rw [measurableCylinders_nat] at hs
          simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
          obtain ⟨n, S, hS, rfl⟩ := hs
          let f : Path → (Fin (n + 1) → Bool) := fun x i => x i.val
          let g : (Fin (n + 1) → Bool) → (↥(Finset.Iic n) → Bool) :=
            fun w i => w ⟨i.val, by have := Finset.mem_Iic.mp i.property; omega⟩
          have he : cylinder (Finset.Iic n) S = f ⁻¹' (g ⁻¹' S) := by
            ext x
            rfl
          have hgS : MeasurableSet (g ⁻¹' S) := hS.preimage (measurable_of_countable g)
          simp_rw [he, ← Measure.map_apply (by fun_prop : Measurable f) hgS]
          exact hprefix n (g ⁻¹' S)
        have hcond (root : Bool) :
            Measurable (fun q : unitInterval => conditionalSourceLaw q root) := by
          let k : Kernel unitInterval Path := ⟨fun q => armLaw q root, harm root⟩
          let : IsMarkovKernel k :=
            ⟨fun q => inferInstanceAs (IsProbabilityMeasure (armLaw q root))⟩
          let f : Path × Path → Source :=
            fun p => (root, (fun i => p.1 (i + 1), fun i => p.2 (i + 1)))
          have hf : Measurable f := by fun_prop
          have he : (fun q : unitInterval => conditionalSourceLaw q root) = (k ×ₖ k).map f := by
            funext q
            rw [Kernel.map_apply _ hf, Kernel.prod_apply]
            rfl
          rw [he]
          exact Kernel.measurable _
        apply Measure.measurable_of_measurable_coe
        intro s hs
        simp only [sourceLaw, Measure.add_apply, Measure.smul_apply]
        exact (measurable_const.mul ((Measure.measurable_coe hs).comp (hcond true))).add
          (measurable_const.mul ((Measure.measurable_coe hs).comp (hcond false)))
      have hjoint : Measurable (jointLaw ν alpha) := by
        let k : Kernel unitInterval Source := ⟨sourceLaw alpha, hsource⟩
        let : IsMarkovKernel k :=
          ⟨fun q => inferInstanceAs (IsProbabilityMeasure (sourceLaw alpha q))⟩
        have he : jointLaw ν alpha = (Kernel.const unitInterval ν ×ₖ k) := by
          funext q
          rw [Kernel.prod_apply]
          rfl
        rw [he]
        exact Kernel.measurable _
      have hprob : IsProbabilityMeasure (priorLaw ν alpha μ) :=
        isProbabilityMeasure_bind hjoint.aemeasurable
          (Filter.Eventually.of_forall fun _ => inferInstance)
      have hsourceProb : IsProbabilityMeasure (μ.bind (sourceLaw alpha)) :=
        isProbabilityMeasure_bind hsource.aemeasurable
          (Filter.Eventually.of_forall fun _ => inferInstance)
      let : IsProbabilityMeasure (priorLaw ν alpha μ) := hprob
      let : IsProbabilityMeasure (μ.bind (sourceLaw alpha)) := hsourceProb
      have heq : priorLaw ν alpha μ = ν.prod (μ.bind (sourceLaw alpha)) := by
        apply Measure.ext_prod
        intro s t hs ht
        rw [priorLaw, Measure.bind_apply (hs.prod ht) hjoint.aemeasurable, Measure.prod_prod,
          Measure.bind_apply ht hsource.aemeasurable]
        simp only [jointLaw, Measure.prod_prod]
        exact lintegral_const_mul (ν s) ((Measure.measurable_coe ht).comp hsource)
      have hstop : Measurable (fun p : Seed × Source => stoppingTime policy p.1 p.2) := by
        classical
        have hchoose : Measurable (fun p : Seed × (List Bool × List Bool) =>
            policy.choose p.1 p.2.1 p.2.2) :=
          measurable_from_prod_countable_left fun ar => policy.measurable_section ar.1 ar.2
        have hrep : ∀ n, Measurable (fun u => zeroReplay policy u n) := by
          intro n
          induction n with
          | zero => exact measurable_const
          | succ n ih =>
            exact (measurable_of_countable (fun p : Bool × List Bool => p.1 :: p.2)).comp
              ((hchoose.comp (measurable_id.prodMk (ih.prodMk measurable_const))).prodMk ih)
        have htail (n : ℕ) : MeasurableSet {p : Seed × Source |
            (n : WithTop ℕ) < stoppingTime policy p.1 p.2} := by
          have he : {p : Seed × Source | (n : WithTop ℕ) < stoppingTime policy p.1 p.2} =
              ⋃ actions : List Bool, {u | zeroReplay policy u n = actions} ×ˢ
                {s | prefixNoMarker s actions} := by
            ext p
            simp only [Set.mem_ofPred_eq]
            rw [(stopped_execution_replay_bridge policy p.1 p.2 n).1]
            simp
          rw [he]
          apply MeasurableSet.iUnion
          intro actions
          apply MeasurableSet.prod ((hrep n) (measurableSet_singleton actions))
          unfold prefixNoMarker markerResponse
          simp only [Set.ofPred_forall]
          refine MeasurableSet.iInter fun side => ?_
          refine MeasurableSet.iInter fun i => ?_
          cases i <;> cases side <;> simp only [endpoint, arm] <;> measurability
        apply measurable_of_Ioi
        intro x
        induction x using WithTop.recTopCoe with
        | top => simp
        | coe n => exact htail n
      have hsum (t : WithTop ℕ) : tauENN t =
          ∑' n : ℕ, if (n : WithTop ℕ) < t then 1 else 0 := by
        classical
        induction t using WithTop.recTopCoe with
        | top => simp [tauENN]
        | coe k =>
            rw [tsum_eq_sum (s := Finset.range k)]
            · calc
                (k : ℝ≥0∞) = ∑ n ∈ Finset.range k, (1 : ℝ≥0∞) := by simp
                _ = ∑ n ∈ Finset.range k, if (n : WithTop ℕ) < (k : WithTop ℕ) then 1 else 0 := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  have hn' : (n : WithTop ℕ) < (k : WithTop ℕ) := by
                    exact_mod_cast (Finset.mem_range.mp hn : n < k)
                  rw [if_pos hn']
            · intro n hn
              simp only [Finset.mem_range, not_lt] at hn
              simp [hn.not_gt]
      refine ⟨hprob, heq, ?_⟩
      unfold expectedCost priorLaw
      have hτ : Measurable (fun p : Seed × Source => tauENN (stoppingTime policy p.1 p.2)) :=
        (measurable_of_countable tauENN).comp hstop
      rw [Measure.lintegral_bind (m := μ) (μ := jointLaw ν alpha)
        (f := fun p : Seed × Source => tauENN (stoppingTime policy p.1 p.2))
        hjoint.aemeasurable hτ.aemeasurable]
      apply lintegral_congr
      intro q
      simp_rw [hsum]
      rw [lintegral_tsum]
      · apply tsum_congr
        intro n
        have hT : MeasurableSet
            {p : Seed × Source | (n : WithTop ℕ) < stoppingTime policy p.1 p.2} :=
          measurableSet_lt measurable_const hstop
        have h := lintegral_indicator_const (μ := jointLaw ν alpha q) hT (1 : ℝ≥0∞)
        simpa only [Set.indicator, Set.mem_ofPred_eq, one_mul] using h
      · intro n
        exact (measurable_const.ite
          (measurableSet_lt measurable_const hstop) measurable_const).aemeasurable
    have hfixed (q : unitInterval) (hq : (q : ℝ) < 1) :
        0 ≤ replayWeight policy ν q ∧ replayWeight policy ν q ≤ 1 ∧
        (∑' n : ℕ, jointLaw ν alpha q {p | (n : WithTop ℕ) < stoppingTime policy p.1 p.2}) =
          ENNReal.ofReal (2 / (1 - (q : ℝ)) - (1 - (alpha : ℝ)) +
            ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * replayWeight policy ν q) := by
      classical
      let T (n : ℕ) : ℝ := (jointLaw ν alpha q).real
        {p | (n : WithTop ℕ) < stoppingTime policy p.1 p.2}
      obtain ⟨hodd, heven, hlam⟩ := adaptive_marker_stopping_tails policy ν alpha q
      have hs : Summable (fun n : ℕ => (q : ℝ) ^ n) :=
        summable_geometric_of_lt_one (unitInterval.nonneg q) hq
      have hw : Summable (fun n : ℕ => lambda policy ν (n + 1) * (q : ℝ) ^ n) :=
        Summable.of_nonneg_of_le
          (fun n => mul_nonneg (hlam _).1 (pow_nonneg (unitInterval.nonneg q) _))
          (fun n => mul_le_of_le_one_left (pow_nonneg (unitInterval.nonneg q) _) (hlam _).2) hs
      have hw0 : 0 ≤ replayWeight policy ν q := by
        exact mul_nonneg (unitInterval.one_minus_nonneg q) (tsum_nonneg (fun n =>
          mul_nonneg (hlam _).1 (pow_nonneg (unitInterval.nonneg q) _)))
      have hw1 : replayWeight policy ν q ≤ 1 := by
        have hle := hw.tsum_le_tsum
          (fun n => mul_le_of_le_one_left (pow_nonneg (unitInterval.nonneg q) _) (hlam _).2) hs
        rw [tsum_geometric_of_lt_one (unitInterval.nonneg q) hq] at hle
        have hx := sub_pos.mpr hq
        dsimp [replayWeight]
        calc
          _ ≤ (1 - (q : ℝ)) * (1 - (q : ℝ))⁻¹ := mul_le_mul_of_nonneg_left hle hx.le
          _ = 1 := mul_inv_cancel₀ hx.ne'
      have h0 : T 0 = 1 := by
        have hsurvive (p : Seed × Source) : (0 : WithTop ℕ) < stoppingTime policy p.1 p.2 :=
          (stopped_execution_replay_bridge policy p.1 p.2 0).1.mpr
            (by simp [prefixNoMarker, zeroReplay, sideCount])
        have he : {p : Seed × Source | (0 : WithTop ℕ) < stoppingTime policy p.1 p.2} = Set.univ :=
          Set.eq_univ_of_forall hsurvive
        simp [T, he]
      have he (n : ℕ) : T (2 * (n + 1)) =
          (q : ℝ) * (q : ℝ) ^ n +
            ((1 - (q : ℝ)) * ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ))) *
              (lambda policy ν (n + 1) * (q : ℝ) ^ n) := by
        rw [show T (2 * (n + 1)) = _ from heven (n + 1) (by omega)]
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
      have hsEvenShift : Summable (fun n : ℕ => T (2 * (n + 1))) := by
        apply ((hs.mul_left (q : ℝ)).add (hw.mul_left
          ((1 - (q : ℝ)) * ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ))))).congr
        intro n
        exact (he n).symm
      have hsEven : Summable (fun n : ℕ => T (2 * n)) := by
        apply (summable_nat_add_iff (f := fun n : ℕ => T (2 * n)) 1).mp
        exact hsEvenShift
      have hsOdd : Summable (fun n : ℕ => T (2 * n + 1)) := by
        apply (hs.mul_left ((alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ))).congr
        intro n
        exact (hodd n).symm
      have hsum : HasSum T
          (2 / (1 - (q : ℝ)) - (1 - (alpha : ℝ)) +
            ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * replayWeight policy ν q) := by
        have hTS : HasSum T ((∑' n : ℕ, T (2 * n)) + (∑' n : ℕ, T (2 * n + 1))) :=
          HasSum.even_add_odd (f := T) hsEven.hasSum hsOdd.hasSum
        have hx : 1 - (q : ℝ) ≠ 0 := (sub_pos.mpr hq).ne'
        have hb : 1 + ((q : ℝ) + ((alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ))) *
            (1 - (q : ℝ))⁻¹ = 2 / (1 - (q : ℝ)) - (1 - (alpha : ℝ)) := by
          field_simp [hx]
          ring
        have heq : ((∑' n : ℕ, T (2 * n)) + (∑' n : ℕ, T (2 * n + 1))) =
            2 / (1 - (q : ℝ)) - (1 - (alpha : ℝ)) +
              ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * replayWeight policy ν q := by
          rw [hsEven.tsum_eq_zero_add, h0]
          simp_rw [he, show ∀ n, T (2 * n + 1) = _ from hodd]
          rw [Summable.tsum_add (hs.mul_left _) (hw.mul_left _), tsum_mul_left, tsum_mul_left,
            tsum_mul_left, tsum_geometric_of_lt_one (unitInterval.nonneg q) hq]
          dsimp only [replayWeight]
          linear_combination hb
        rw [heq] at hTS
        exact hTS
      refine ⟨hw0, hw1, ?_⟩
      have hm (n : ℕ) : jointLaw ν alpha q {p | (n : WithTop ℕ) < stoppingTime policy p.1 p.2} =
          ENNReal.ofReal (T n) := by
        dsimp [T, measureReal_def]
        exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      calc
        _ = ∑' n : ℕ, ENNReal.ofReal (T n) := tsum_congr hm
        _ = ENNReal.ofReal (∑' n : ℕ, T n) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hsum.summable).symm
        _ = _ := by rw [hsum.tsum_eq]
    let E (q : unitInterval) : ℝ := 2 / (1 - (q : ℝ)) - (1 - (alpha : ℝ)) +
      ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * replayWeight policy ν q
    have hcost : expectedCost policy ν alpha μ = ∫⁻ q, ENNReal.ofReal (E q) ∂μ := by
      rw [hbridge.2.2]
      apply lintegral_congr_ae
      filter_upwards [hQ] with q hq
      exact (hfixed q hq.2).2.2
    have hI : reciprocalMoment μ = ∫⁻ q : unitInterval,
        ENNReal.ofReal (1 / (1 - (q : ℝ))) ∂μ := by
      unfold reciprocalMoment
      apply lintegral_congr_ae
      filter_upwards [hQ] with q hq
      rw [one_div, ENNReal.ofReal_inv_of_pos (sub_pos.mpr hq.2)]
    have hbound (q : unitInterval) (hq : (q : ℝ) < 1) :
        (alpha : ℝ) / (1 - (q : ℝ)) ≤ E q ∧ E q ≤ 1 + 2 / (1 - (q : ℝ)) := by
      have hR0 := (hfixed q hq).1
      have hR1 := (hfixed q hq).2.1
      have hq0 := unitInterval.nonneg q
      have ha0 : 0 < 1 - (alpha : ℝ) := sub_pos.mpr ha.2
      have hqR0 : 0 ≤ (q : ℝ) * replayWeight policy ν q := mul_nonneg hq0 hR0
      have hqR1 : (q : ℝ) * replayWeight policy ν q ≤ 1 :=
        mul_le_one₀ (unitInterval.le_one q) hR0 hR1
      have haR0 : 0 ≤ (alpha : ℝ) * replayWeight policy ν q := mul_nonneg ha.1.le hR0
      have haR1 : (alpha : ℝ) * replayWeight policy ν q ≤ (alpha : ℝ) :=
        mul_le_of_le_one_right ha.1.le hR1
      have hinv : 1 ≤ 1 / (1 - (q : ℝ)) :=
        (le_div_iff₀ (sub_pos.mpr hq)).mpr (by simpa using unitInterval.one_minus_le_one q)
      have hadiv : (1 - (alpha : ℝ)) ≤ (1 - (alpha : ℝ)) * (1 / (1 - (q : ℝ))) :=
        le_mul_of_one_le_right ha0.le hinv
      dsimp [E]
      simp only [div_eq_mul_inv, one_mul] at *
      constructor <;> nlinarith
    have hlo : ENNReal.ofReal (alpha : ℝ) * reciprocalMoment μ ≤ expectedCost policy ν alpha μ := by
      rw [hcost, hI, ← lintegral_const_mul _ (by fun_prop)]
      apply lintegral_mono_ae
      filter_upwards [hQ] with q hq
      rw [← ENNReal.ofReal_mul ha.1.le]
      apply ENNReal.ofReal_le_ofReal
      simpa only [div_eq_mul_inv, one_div, one_mul] using (hbound q hq.2).1
    have hup : expectedCost policy ν alpha μ ≤ 1 + 2 * reciprocalMoment μ := by
      rw [hcost, hI]
      calc
        _ ≤ ∫⁻ q : unitInterval, ENNReal.ofReal (1 + 2 / (1 - (q : ℝ))) ∂μ := by
          apply lintegral_mono_ae
          exact hQ.mono (fun q hq => ENNReal.ofReal_le_ofReal (hbound q hq.2).2)
        _ = 1 + 2 * ∫⁻ q : unitInterval, ENNReal.ofReal (1 / (1 - (q : ℝ))) ∂μ := by
          have he (q : unitInterval) : ENNReal.ofReal (1 + 2 / (1 - (q : ℝ))) =
              1 + 2 * ENNReal.ofReal (1 / (1 - (q : ℝ))) := by
            rw [ENNReal.ofReal_add zero_le_one
              (div_nonneg (by norm_num) (unitInterval.one_minus_nonneg q)), ENNReal.ofReal_one]
            rw [show 2 / (1 - (q : ℝ)) = 2 * (1 / (1 - (q : ℝ))) by ring,
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          simp_rw [he]
          rw [lintegral_add_left measurable_const, lintegral_const_mul _ (by fun_prop)]
          simp
    have hfin : expectedCost policy ν alpha μ ≠ ⊤ ↔ reciprocalMoment μ ≠ ⊤ := by
      constructor
      · intro hc hItop
        rw [hItop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr ha.1))] at hlo
        exact hc (top_unique hlo)
      · intro hIne
        exact ne_top_of_le_ne_top (by finiteness) hup
    refine ⟨hlo, hup, hfin, ?_⟩
    intro hIne
    have hInv0 : ∀ q : unitInterval, 0 ≤ 1 / (1 - (q : ℝ)) :=
      fun q => div_nonneg zero_le_one (unitInterval.one_minus_nonneg q)
    have hInv : Integrable (fun q : unitInterval => 1 / (1 - (q : ℝ))) μ :=
      (lintegral_ofReal_ne_top_iff_integrable
        ((measurable_const.div
          (measurable_const.sub measurable_subtype_coe)).aestronglyMeasurable)
        (Filter.Eventually.of_forall hInv0)).mp (hI ▸ hIne)
    have hIreal : (reciprocalMoment μ).toReal = ∫ q : unitInterval, 1 / (1 - (q : ℝ)) ∂μ := by
      rw [hI, ← ofReal_integral_eq_lintegral_ofReal hInv (Filter.Eventually.of_forall hInv0),
        ENNReal.toReal_ofReal (integral_nonneg hInv0)]
    have hRmeas : Measurable (replayWeight policy ν) := by
      unfold replayWeight
      exact (measurable_const.sub measurable_subtype_coe).mul
        (Measurable.tsum (fun n => measurable_const.mul (measurable_subtype_coe.pow_const n)))
    have hDint : Integrable (fun q : unitInterval =>
        ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * replayWeight policy ν q) μ := by
      apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
      filter_upwards [hQ] with q hq
      have hR0 := (hfixed q hq.2).1
      have hR1 := (hfixed q hq.2).2.1
      have hq0 := unitInterval.nonneg q
      have hq1 := unitInterval.le_one q
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> nlinarith [mul_nonneg hq0 hR0,
        mul_le_one₀ hq1 hR0 hR1]
    have hbaseint : Integrable (fun q : unitInterval =>
        2 * (1 / (1 - (q : ℝ))) - (1 - (alpha : ℝ))) μ :=
      (hInv.const_mul 2).sub (integrable_const _)
    have hEint : Integrable E μ := by
      convert hbaseint.add hDint using 1
      all_goals first | rfl | (ext q; dsimp [E]; ring)
    have hE0 : ∀ᵐ q ∂μ, 0 ≤ E q := hQ.mono (fun q hq =>
      (div_nonneg ha.1.le (unitInterval.one_minus_nonneg q)).trans (hbound q hq.2).1)
    have hEreal : (expectedCost policy ν alpha μ).toReal = ∫ q, E q ∂μ := by
      rw [hcost, ← ofReal_integral_eq_lintegral_ofReal hEint hE0,
        ENNReal.toReal_ofReal (integral_nonneg_of_ae hE0)]
    have hlambda := (adaptive_marker_stopping_tails policy ν alpha (0 : unitInterval)).2.2
    have hsum := hcorrections.2.2 (fun n => lambda policy ν (n + 1)) (fun n => hlambda (n + 1))
    rw [hEreal, hIreal]
    dsimp only [E]
    simp only [show ∀ q : unitInterval,
      2 / (1 - (q : ℝ)) = 2 * (1 / (1 - (q : ℝ))) from (fun q => by ring)]
    rw [integral_add (f := fun q : unitInterval => 2 * (1 / (1 - (q : ℝ))) - (1 - (alpha : ℝ)))
        (g := fun q : unitInterval =>
          ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * replayWeight policy ν q)
        hbaseint hDint,
      integral_sub (f := fun q : unitInterval => 2 * (1 / (1 - (q : ℝ))))
        (g := fun _ : unitInterval => 1 - (alpha : ℝ))
        (hInv.const_mul 2) (integrable_const _), integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    congr 1
    rw [hsum.tsum_eq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => by dsimp [replayWeight]; ring)
  have hpulse {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed)
      [IsProbabilityMeasure ν] (N : ℕ) (hN : 1 ≤ N) :
      ∀ m, lambda (pulse N) ν m = if m = N then 1 else 0 := by
    classical
    have hlen (u : Seed) : ∀ n, (zeroReplay (pulse N) u n).length = n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp [zeroReplay, ih]
    have hr (u : Seed) : ∀ n,
        sideCount (zeroReplay (pulse N) u n) true =
          (if 2 * N ≤ n then 1 else 0) + (if 2 * N + 1 ≤ n then 1 else 0) := by
      intro n
      induction n with
      | zero => simp [zeroReplay, sideCount]; omega
      | succ n ih =>
        have hc : (pulse N).choose u (zeroReplay (pulse N) u n) (List.replicate n false) =
            decide (n + 1 = 2 * N ∨ n + 1 = 2 * N + 1) := by
          change decide ((zeroReplay (pulse N) u n).length + 1 = 2 * N ∨
            (zeroReplay (pulse N) u n).length + 1 = 2 * N + 1) = _
          rw [hlen]
        change List.count true ((pulse N).choose u (zeroReplay (pulse N) u n)
          (List.replicate n false) :: zeroReplay (pulse N) u n) = _
        rw [List.count_cons, hc]
        simp only [beq_iff_eq, decide_eq_true_eq]
        change sideCount (zeroReplay (pulse N) u n) true + _ = _
        rw [ih]
        split_ifs <;> omega
    have hcounts (actions : List Bool) :
        sideCount actions false + sideCount actions true = actions.length := by
      induction actions with
      | nil => simp [sideCount]
      | cons side actions ih =>
        cases side <;>
          simpa [sideCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            congrArg Nat.succ ih
    have hpar (u : Seed) (m : ℕ) :
        (sideCount (zeroReplay (pulse N) u (2 * m)) false % 2 = 1 ∧
          sideCount (zeroReplay (pulse N) u (2 * m)) true % 2 = 1) ↔ m = N := by
      have hc := hcounts (zeroReplay (pulse N) u (2 * m))
      rw [hlen] at hc
      have hright := hr u (2 * m)
      split_ifs at hright <;> omega
    intro m
    unfold lambda
    simp_rw [hpar]
    by_cases hm : m = N <;> simp [hm]
  have hleftlambda {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed)
      [IsProbabilityMeasure ν] : ∀ m, lambda (alwaysLeft : Policy Seed) ν m = 0 := by
    have hrep (u : Seed) :
        ∀ n, zeroReplay (alwaysLeft : Policy Seed) u n = List.replicate n false := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          change false :: zeroReplay (alwaysLeft : Policy Seed) u n = List.replicate (n + 1) false
          rw [ih, List.replicate_succ]
    intro m
    unfold lambda
    simp [hrep, sideCount]
  have hleft {Seed : Type u} [MeasurableSpace Seed] (ν : Measure Seed)
      [IsProbabilityMeasure ν] (hI : reciprocalMoment μ ≠ ⊤) :
      (expectedCost (alwaysLeft : Policy Seed) ν alpha μ).toReal =
        2 * (reciprocalMoment μ).toReal - (1 - (alpha : ℝ)) := by
    simpa [hleftlambda ν] using (hall (alwaysLeft : Policy Seed) ν).2.2.2 hI
  have hnonnegative (hr : ¬ (alpha : ℝ) / (1 - (alpha : ℝ)) <
      essSup (fun q : unitInterval => (q : ℝ)) μ) :
      ∀ n, 0 ≤ coefficient alpha μ (n + 1) := by
    intro n
    by_contra hn
    have hn' : coefficient alpha μ (n + 1) < 0 := lt_of_not_ge hn
    have hnf : firstNegative alpha μ < ⊤ := by
      rw [firstNegative, sInf_lt_iff]
      exact ⟨((n + 1 : ℕ) : WithTop ℕ), ⟨n + 1, ⟨by omega, hn'⟩, rfl⟩, by simp⟩
    exact hr (hsupport.1.mp hnf)
  have hminimum {Seed : Type u} [MeasurableSpace Seed] (policy : Policy Seed)
      (ν : Measure Seed) [IsProbabilityMeasure ν] (hI : reciprocalMoment μ ≠ ⊤)
      (hv : ∀ n, 0 ≤ coefficient alpha μ (n + 1)) :
      expectedCost alwaysLeft ν alpha μ ≤ expectedCost policy ν alpha μ := by
    have hp := hall policy ν
    have hl := hall (alwaysLeft : Policy Seed) ν
    apply (ENNReal.toReal_le_toReal (hl.2.2.1.mpr hI) (hp.2.2.1.mpr hI)).mp
    rw [hleft ν hI, hp.2.2.2 hI]
    have hlambdaBound := (adaptive_marker_stopping_tails policy ν alpha (0 : unitInterval)).2.2
    have hsum0 : 0 ≤ ∑' n : ℕ, lambda policy ν (n + 1) * coefficient alpha μ (n + 1) :=
      tsum_nonneg (fun n => mul_nonneg (hlambdaBound (n + 1)).1 (hv n))
    linarith
  refine ⟨hsupport.1, ⟨hcorrections.1, hcorrections.2.1, ?_⟩,
    @hall, @hleft, ?_, ?_, ?_, ?_⟩
  · intro Seed _ policy ν _
    have hl := (adaptive_marker_stopping_tails policy ν alpha (0 : unitInterval)).2.2
    exact (hcorrections.2.2 _ (fun n => hl (n + 1))).summable
  · intro Seed _ ν _ hI
    constructor
    · rintro ⟨policy, hp⟩
      by_contra hr
      exact (not_lt_of_ge (hminimum policy ν hI (hnonnegative hr))) hp
    · intro hr
      have hnf := hsupport.1.mpr hr
      rw [firstNegative, sInf_lt_iff] at hnf
      obtain ⟨k, ⟨N, ⟨hN, hvN⟩, rfl⟩, hk⟩ := hnf
      refine ⟨pulse N, ?_⟩
      have hp := hall (pulse N : Policy Seed) ν
      have hl := hall (alwaysLeft : Policy Seed) ν
      apply (ENNReal.toReal_lt_toReal (hp.2.2.1.mpr hI) (hl.2.2.1.mpr hI)).mp
      rw [hp.2.2.2 hI, hleft ν hI]
      have hsum : (∑' n : ℕ, lambda (pulse N) ν (n + 1) * coefficient alpha μ (n + 1)) =
          coefficient alpha μ N := by
        simp_rw [hpulse ν N hN]
        rw [tsum_eq_single (N - 1)]
        · have hNsub : N - 1 + 1 = N := by omega
          simp [hNsub]
        · intro n hn
          have hne : n + 1 ≠ N := by omega
          simp [hne]
      rw [hsum]
      linarith
  · intro hhalf
    have hpos := hsupport.2 hhalf
    refine ⟨hpos, ?_, ?_⟩
    · apply eq_top_iff.mpr
      by_contra hn
      have hnf : firstNegative alpha μ < ⊤ := lt_of_not_ge hn
      rw [firstNegative, sInf_lt_iff] at hnf
      obtain ⟨k, ⟨m, ⟨hm, hvm⟩, rfl⟩, hk⟩ := hnf
      exact (hpos m hm).not_gt hvm
    · intro Seed _ policy ν _ hI
      exact hminimum policy ν hI (fun n => (hpos (n + 1) (by omega)).le)
  · intro Seed Seed' _ _ policy policy' ν ν' _ _ hπ hπ'
    have hp := hall policy ν
    have hp' := hall policy' ν'
    have hI := hp.2.2.1.mp hπ
    rw [hp.2.2.2 hI, hp'.2.2.2 hI]
    have hl := (adaptive_marker_stopping_tails policy ν alpha (0 : unitInterval)).2.2
    have hl' := (adaptive_marker_stopping_tails policy' ν' alpha (0 : unitInterval)).2.2
    let f (n : ℕ) := lambda policy ν (n + 1) * coefficient alpha μ (n + 1)
    let g (n : ℕ) := lambda policy' ν' (n + 1) * coefficient alpha μ (n + 1)
    have hfs : Summable f := (hcorrections.2.2 _ (fun n => hl (n + 1))).summable
    have hgs : Summable g := (hcorrections.2.2 _ (fun n => hl' (n + 1))).summable
    have hbound (n : ℕ) : |f n - g n| ≤ |coefficient alpha μ (n + 1)| := by
      have h1 := hl (n + 1)
      have h2 := hl' (n + 1)
      have hle : |lambda policy ν (n + 1) - lambda policy' ν' (n + 1)| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> linarith
      dsimp [f, g]
      rw [← sub_mul, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hle
    have has : Summable (fun n => |f n - g n|) :=
      Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbound hcorrections.1
    have hnorm : |(∑' n, (f n - g n))| ≤ ∑' n, |f n - g n| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
        (f := fun n => f n - g n) (by simpa only [Real.norm_eq_abs] using has)
    have heq : (2 * (reciprocalMoment μ).toReal - (1 - (alpha : ℝ)) + ∑' n, f n) -
        (2 * (reciprocalMoment μ).toReal - (1 - (alpha : ℝ)) + ∑' n, g n) =
        ∑' n, (f n - g n) := by rw [hfs.tsum_sub hgs]; ring
    change |(2 * (reciprocalMoment μ).toReal - (1 - (alpha : ℝ)) + ∑' n, f n) -
      (2 * (reciprocalMoment μ).toReal - (1 - (alpha : ℝ)) + ∑' n, g n)| < 1
    rw [heq]
    exact (hnorm.trans (has.tsum_le_tsum hbound hcorrections.1)).trans_lt hcorrections.2.1
  · intro hItop Seed _ policy ν _
    have htop (p : Policy Seed) : expectedCost p ν alpha μ = ⊤ := by
      have h := (hall p ν).2.2.1
      by_contra hn
      exact (h.mp hn) hItop
    exact ⟨htop policy, by rw [htop policy, htop alwaysLeft]; simp⟩

end D5.S3.Observer.ProbabilisticClosure.BeneficialMarkerDeflection
