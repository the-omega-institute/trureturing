/- GID: D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit
   generality: I
   mirror-B: D5/B/S3/Analytic/MomentMinors/BoundedFifthMomentLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp Meer–Weeks fifth central moment bounds for laws bounded on one side. -/

import D5.S3.Analytic.MomentMinors.Defs
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open MeasureTheory ProbabilityTheory
open D5.S3.Analytic.MomentMinors.Defs (mean)

namespace D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit

/-- The standardized fifth moment of the extremal two-point law. -/
def fifthBound (z : ℝ) : ℝ := z ^ 3 - z + z⁻¹ - z⁻¹ ^ 3

/-- The fifth central moment bounds for arbitrary real probability laws with
finite fifth absolute moment and positive variance. -/
def claim : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
    Integrable (fun x : ℝ => |x| ^ 5) μ → 0 < centralMoment id 2 μ →
    (∀ L : ℝ, (∀ᵐ x ∂μ, L ≤ x) →
      fifthBound (Real.sqrt (centralMoment id 2 μ) / (mean μ - L)) ≤
        centralMoment id 5 μ / Real.sqrt (centralMoment id 2 μ) ^ 5) ∧
    (∀ U : ℝ, (∀ᵐ x ∂μ, x ≤ U) →
      centralMoment id 5 μ / Real.sqrt (centralMoment id 2 μ) ^ 5 ≤
        -fifthBound (Real.sqrt (centralMoment id 2 μ) / (U - mean μ)))

private lemma integrable_centered_pow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ => |x| ^ 5) μ) (c : ℝ) (k : ℕ) (hk : k ≤ 5) :
    Integrable (fun x : ℝ => (x - c) ^ k) μ := by
  sorry

private lemma mean_gap_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ => |x| ^ 5) μ) (hv : 0 < centralMoment id 2 μ)
    (L : ℝ) (hL : ∀ᵐ x ∂μ, L ≤ x) : 0 < mean μ - L := by
  sorry

private lemma polynomial_minorant (a b y : ℝ) (hy : -a ≤ y) :
    (-a ^ 3 + 2 * a ^ 2 * b - 3 * a * b ^ 2 + 4 * b ^ 3) * y ^ 2 +
      (2 * a ^ 3 * b - 4 * a ^ 2 * b ^ 2 + 6 * a * b ^ 3 - 3 * b ^ 4) * y +
      (-a ^ 3 * b ^ 2 + 2 * a ^ 2 * b ^ 3 - 3 * a * b ^ 4) ≤ y ^ 5 := by
  sorry

private lemma integrated_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ => |x| ^ 5) μ) (L : ℝ)
    (hL : ∀ᵐ x ∂μ, L ≤ x) (ha : 0 < mean μ - L) :
    let a := mean μ - L
    let b := centralMoment id 2 μ / a
    a * b * (b - a) * (a ^ 2 + b ^ 2) ≤ centralMoment id 5 μ := by
  sorry

private lemma normalization (a v M : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hM : a * (v / a) * (v / a - a) * (a ^ 2 + (v / a) ^ 2) ≤ M) :
    fifthBound (Real.sqrt v / a) ≤ M / Real.sqrt v ^ 5 := by
  sorry

private lemma lower_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ => |x| ^ 5) μ) (hv : 0 < centralMoment id 2 μ)
    (L : ℝ) (hL : ∀ᵐ x ∂μ, L ≤ x) :
    fifthBound (Real.sqrt (centralMoment id 2 μ) / (mean μ - L)) ≤
      centralMoment id 5 μ / Real.sqrt (centralMoment id 2 μ) ^ 5 := by
  have ha := mean_gap_pos μ h hv L hL
  exact normalization _ _ _ ha hv (integrated_bound μ h L hL ha)

private lemma upper_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Integrable (fun x : ℝ => |x| ^ 5) μ) (hv : 0 < centralMoment id 2 μ)
    (U : ℝ) (hU : ∀ᵐ x ∂μ, x ≤ U) :
    centralMoment id 5 μ / Real.sqrt (centralMoment id 2 μ) ^ 5 ≤
      -fifthBound (Real.sqrt (centralMoment id 2 μ) / (U - mean μ)) := by
  sorry

/-- Both one-sided Meer–Weeks fifth-moment inequalities. -/
theorem result : claim := by
  intro μ _ h hv
  exact ⟨fun L hL => lower_bound μ h hv L hL, fun U hU => upper_bound μ h hv U hU⟩

end D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit
