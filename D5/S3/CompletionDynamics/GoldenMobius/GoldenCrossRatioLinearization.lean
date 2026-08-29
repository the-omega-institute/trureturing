/- GID: D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization
   generality: I
   mirror-B: D5/B/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden cross-ratio coordinates conjugate the reciprocal Mobius map
     exactly to multiplication by minus the inverse golden ratio squared. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
import Mathlib.Logic.Function.Iterate

/-!
The source identity is a genuine exact conjugacy, rather than an asymptotic
linearization. Because the affine formulas use totalized division in Lean, the
geometric theorem explicitly excludes the pole `0` of `T` and the pole `ψ` of
the cross-ratio chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.GoldenMobius.GoldenCrossRatioLinearization

open scoped goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap

/-- Projective coordinate sending the attracting golden fixed point to zero and
the conjugate fixed point to the point at infinity. -/
def goldenCrossRatio (x : ℝ) : ℝ :=
  (x - Real.goldenRatio) / (x - Real.goldenConj)

@[simp]
theorem golden_cross_ratio_at_golden :
    goldenCrossRatio Real.goldenRatio = 0 := by
  simp [goldenCrossRatio]

/-- The numerator of the transformed cross-ratio in denominator-separated
form. -/
theorem golden_mobius_sub_golden {x : ℝ} (hx : x ≠ 0) :
    goldenMobius x - Real.goldenRatio =
      -(x - Real.goldenRatio) / (Real.goldenRatio * x) := by
  have hPhiX : Real.goldenRatio * x ≠ 0 :=
    mul_ne_zero Real.goldenRatio_ne_zero hx
  apply (eq_div_iff hPhiX).2
  unfold goldenMobius
  field_simp [hx]
  nlinarith [Real.goldenRatio_sq]

/-- The denominator of the transformed cross-ratio in denominator-separated
form. -/
theorem golden_mobius_sub_conjugate {x : ℝ} (hx : x ≠ 0) :
    goldenMobius x - Real.goldenConj =
      Real.goldenRatio * (x - Real.goldenConj) / x := by
  apply (eq_div_iff hx).2
  unfold goldenMobius
  field_simp [hx]
  nlinarith [Real.goldenRatio_add_goldenConj,
    Real.goldenRatio_mul_goldenConj]

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

/-- Every positive point avoids both affine-chart singularities. -/
theorem positive_avoids_golden_singularities {x : ℝ} (hx : 0 < x) :
    x ≠ 0 ∧ x ≠ Real.goldenConj := by
  constructor
  · exact ne_of_gt hx
  · intro h
    rw [h] at hx
    linarith [Real.goldenConj_neg]

/-- Positivity is invariant under every finite golden Mobius iterate. -/
theorem golden_mobius_iterate_pos (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (goldenMobius^[n]) x := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (golden_mobius_pos hx)

/-- The exact one-step conjugacy iterates to an exact geometric law on the
positive affine chart. -/
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

/-- Fixed-point probe: exact linearization correctly sends the complete point
to zero at every finite depth. -/
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
