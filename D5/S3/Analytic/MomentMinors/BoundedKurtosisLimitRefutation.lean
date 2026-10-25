/- GID: D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.claim; result=D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.result; claim=D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.claim
   digest: A three-point probability law violates the Meer–Weeks two-sided kurtosis limits. -/

import D5.S3.Analytic.MomentMinors.Defs
import Mathlib.Probability.Moments.Basic

/-! A symmetric three-point law exceeds the proposed bidisperse kurtosis upper bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open D5.S3.Analytic.MomentMinors.Defs (mean)

namespace D5.S3.Analytic.MomentMinors.BoundedKurtosisLimitRefutation

/-- The bidisperse standardized fourth moment at an extremal distance. -/
def kurtosisBound (δ δm : ℝ) : ℝ := (δ / δm - δm / δ) ^ 2 + 1

/-- The two-sided Meer–Weeks kurtosis limits for bounded real probability laws. -/
def claim : Prop :=
  ∀ (L U : ℝ), L < U → ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    (∀ᵐ x ∂μ, L ≤ x ∧ x ≤ U) →
    0 < mean μ → 0 < centralMoment id 2 μ →
    let σ := Real.sqrt (centralMoment id 2 μ)
    let δ := σ / mean μ
    let δmin := |1 - L / mean μ|
    let δmax := |1 - U / mean μ|
    let δ₁ := min δmin δmax
    let δ₂ := max δmin δmax
    let δ' := Real.sqrt (δ₁ * δ₂)
    let D4 := centralMoment id 4 μ / centralMoment id 2 μ ^ 2
    (δ < δ₁ → 1 ≤ D4 ∧ D4 ≤ kurtosisBound δ δ₂) ∧
      (δ₁ ≤ δ → δ < δ' → kurtosisBound δ δ₁ ≤ D4 ∧ D4 ≤ kurtosisBound δ δ₂)

private def witness : Measure ℝ :=
  (1 / 4 : ℝ≥0∞) • Measure.dirac 1 +
    (1 / 2 : ℝ≥0∞) • Measure.dirac 2 +
    (1 / 4 : ℝ≥0∞) • Measure.dirac 3

private lemma witness_probability : IsProbabilityMeasure witness := by
  constructor
  norm_num [witness, Measure.add_apply, Measure.smul_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]

private lemma witness_bounds : ∀ᵐ x ∂witness, (1 : ℝ) ≤ x ∧ x ≤ 3 := by
  unfold witness
  simp only [ae_add_measure_iff]
  constructor
  · constructor
    · apply Measure.ae_smul_measure
      norm_num [ae_dirac_eq]
    · apply Measure.ae_smul_measure
      norm_num [ae_dirac_eq]
  · apply Measure.ae_smul_measure
    norm_num [ae_dirac_eq]

private lemma integral_witness (f : ℝ → ℝ) :
    (∫ x, f x ∂witness) = f 1 / 4 + f 2 / 2 + f 3 / 4 := by
  have h1 : Integrable f ((1 / 4 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by finiteness)
  have h2 : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac (2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by finiteness)
  have h3 : Integrable f ((1 / 4 : ℝ≥0∞) • Measure.dirac (3 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by finiteness)
  rw [witness, integral_add_measure (h1.add_measure h2) h3,
    integral_add_measure h1 h2]
  norm_num [integral_smul_measure, integral_dirac, smul_eq_mul]
  ring

private lemma mean_witness : mean witness = 2 := by
  unfold mean
  rw [integral_witness]
  norm_num

private lemma moment_two_witness : centralMoment id 2 witness = 1 / 2 := by
  unfold centralMoment
  change (∫ x : ℝ, (x - mean witness) ^ 2 ∂witness) = 1 / 2
  rw [mean_witness, integral_witness]
  norm_num

private lemma moment_four_witness : centralMoment id 4 witness = 1 / 2 := by
  unfold centralMoment
  change (∫ x : ℝ, (x - mean witness) ^ 4 ∂witness) = 1 / 2
  rw [mean_witness, integral_witness]
  norm_num

private lemma coefficient_lt : Real.sqrt (1 / 2) / 2 < (1 / 2 : ℝ) := by
  have hs : Real.sqrt (1 / 2) < (1 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  linarith

private lemma bound_value : kurtosisBound (Real.sqrt (1 / 2) / 2) (1 / 2) = 3 / 2 := by
  let s : ℝ := Real.sqrt (1 / 2)
  have hs2 : s ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hi : (1 / 2 : ℝ) / (s / 2) = 2 * s := by
    dsimp only [s]
    rw [div_div_eq_mul_div, mul_comm (1 / 2 : ℝ), mul_div_assoc, Real.div_sqrt]
  unfold kurtosisBound
  change (s / 2 / (1 / 2) - (1 / 2) / (s / 2)) ^ 2 + 1 = 3 / 2
  rw [hi, show s / 2 / (1 / 2) = s by ring]
  nlinarith only [hs2]

/-- The three-point law with masses `1/4, 1/2, 1/4` on `1, 2, 3` violates the upper limit. -/
theorem result : ¬ claim := by
  intro h
  have : IsProbabilityMeasure witness := witness_probability
  have hm : 0 < mean witness := by rw [mean_witness]; norm_num
  have hv : 0 < centralMoment id 2 witness := by rw [moment_two_witness]; norm_num
  have hc := h 1 3 (by norm_num) witness witness_bounds hm hv
  dsimp only at hc
  rw [mean_witness, moment_two_witness, moment_four_witness] at hc
  norm_num only [div_self, one_div, show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num,
    show |(1 : ℝ) - 3 / 2| = 1 / 2 by norm_num, min_self, max_self] at hc
  have hu := (hc.1 coefficient_lt).2
  rw [bound_value] at hu
  norm_num at hu

end D5.S3.Analytic.MomentMinors.BoundedKurtosisLimitRefutation
