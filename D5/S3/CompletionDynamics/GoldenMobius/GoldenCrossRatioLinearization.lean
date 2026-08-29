/- GID: D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization
   generality: I
   mirror-B: D5/B/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden cross-ratio coordinates exactly linearize the Mobius map. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
import Mathlib.Logic.Function.Iterate

/-!
The identity is an exact conjugacy. Since real division is total in Lean, the
geometric theorem explicitly excludes the pole `0` of the Mobius map and the
pole `goldenConj` of the cross-ratio chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.GoldenMobius.GoldenCrossRatioLinearization

open scoped goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap

/-- Projective coordinate sending the attracting fixed point to zero. -/
def goldenCrossRatio (x : ℝ) : ℝ :=
  (x - Real.goldenRatio) / (x - Real.goldenConj)

@[simp]
theorem golden_cross_ratio_at_golden :
    goldenCrossRatio Real.goldenRatio = 0 := by
  simp [goldenCrossRatio]

/-- Numerator identity in a denominator-separated form. -/
theorem golden_mobius_sub_golden {x : ℝ} (hx : x ≠ 0) :
    goldenMobius x - Real.goldenRatio =
      -(x - Real.goldenRatio) / (Real.goldenRatio * x) := by
  have hOneSub : 1 - Real.goldenRatio = Real.goldenConj := by
    linarith [Real.goldenRatio_add_goldenConj]
  have hConjInv :
      Real.goldenConj = -Real.goldenRatio⁻¹ := by
    rw [Real.inv_goldenRatio]
    ring
  calc
    goldenMobius x - Real.goldenRatio =
        (1 - Real.goldenRatio) + 1 / x := by
      unfold goldenMobius
      ring
    _ = Real.goldenConj + 1 / x := by rw [hOneSub]
    _ = -Real.goldenRatio⁻¹ + 1 / x := by rw [hConjInv]
    _ = -(x - Real.goldenRatio) /
        (Real.goldenRatio * x) := by
      field_simp [hx, Real.goldenRatio_ne_zero]
      ring

/-- Denominator identity in a denominator-separated form. -/
theorem golden_mobius_sub_conjugate {x : ℝ} (hx : x ≠ 0) :
    goldenMobius x - Real.goldenConj =
      Real.goldenRatio * (x - Real.goldenConj) / x := by
  have hOneSub : 1 - Real.goldenConj = Real.goldenRatio := by
    linarith [Real.goldenRatio_add_goldenConj]
  calc
    goldenMobius x - Real.goldenConj =
        (1 - Real.goldenConj) + 1 / x := by
      unfold goldenMobius
      ring
    _ = Real.goldenRatio + 1 / x := by rw [hOneSub]
    _ = Real.goldenRatio * (x - Real.goldenConj) / x := by
      apply (eq_div_iff hx).2
      calc
        (Real.goldenRatio + 1 / x) * x =
            Real.goldenRatio * x + 1 := by
          field_simp [hx]
        _ = Real.goldenRatio * (x - Real.goldenConj) := by
          rw [mul_sub, Real.goldenRatio_mul_goldenConj]

/-- Exact golden projective linearization. -/
theorem golden_cross_ratio_linearization {x : ℝ}
    (hx : x ≠ 0) (hConj : x ≠ Real.goldenConj) :
    goldenCrossRatio (goldenMobius x) =
      goldenProjectiveMultiplier * goldenCrossRatio x := by
  unfold goldenCrossRatio
  rw [golden_mobius_sub_golden hx,
    golden_mobius_sub_conjugate hx]
  unfold goldenProjectiveMultiplier
  field_simp [hx, hConj, Real.goldenRatio_ne_zero]
  ring

/-- Positive points avoid both affine-chart singularities. -/
theorem positive_avoids_golden_singularities {x : ℝ} (hx : 0 < x) :
    x ≠ 0 ∧ x ≠ Real.goldenConj := by
  constructor
  · exact ne_of_gt hx
  · intro h
    rw [h] at hx
    linarith [Real.goldenConj_neg]

/-- Positivity is invariant under every finite Mobius iterate. -/
theorem golden_mobius_iterate_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (goldenMobius^[n]) x := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (golden_mobius_pos hx)

/-- Exact geometric contraction law on the positive affine chart. -/
theorem golden_cross_ratio_iterate (n : ℕ) {x : ℝ} (hx : 0 < x) :
    goldenCrossRatio ((goldenMobius^[n]) x) =
      goldenProjectiveMultiplier ^ n * goldenCrossRatio x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      rw [ih (golden_mobius_pos hx)]
      have hDomain := positive_avoids_golden_singularities hx
      rw [golden_cross_ratio_linearization hDomain.1 hDomain.2]
      rw [pow_succ]
      ring

/-- The complete point remains the zero cross-ratio at every depth. -/
example (n : ℕ) :
    goldenCrossRatio ((goldenMobius^[n]) Real.goldenRatio) = 0 := by
  rw [golden_cross_ratio_iterate n Real.goldenRatio_pos,
    golden_cross_ratio_at_golden, mul_zero]

#print axioms golden_mobius_sub_golden
#print axioms golden_mobius_sub_conjugate
#print axioms golden_cross_ratio_linearization
#print axioms golden_mobius_iterate_pos
#print axioms golden_cross_ratio_iterate

end D5.S3.CompletionDynamics.GoldenMobius.GoldenCrossRatioLinearization
