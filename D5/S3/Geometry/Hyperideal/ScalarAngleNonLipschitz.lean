/- GID: D5/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/ScalarAngleNonLipschitz
   mirror-E: none(waiver:scalar-angle-non-lipschitz)
   anchors: []
   utility: none
   digest: The scalar hyperideal extension angle has an explicit square-root cusp. -/

import D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Geometry.Hyperideal.ScalarAngleNonLipschitz

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum

/-- The first-slot scalar path from Section 68, with only the fourth coordinate varying. -/
def scalarPathCosine (ε : ℝ) : ℝ :=
  cosine 2 2 2 (17 - ε) 2 2

/-- The clipped extension angle along the scalar path. -/
def scalarPathAngle (ε : ℝ) : ℝ :=
  Real.arccos (max (-1) (min (scalarPathCosine ε) 1))

/-- Direct substitution gives the affine cosine branch used by the cusp. -/
theorem scalarPathCosine_eq (ε : ℝ) :
    scalarPathCosine ε = -1 + ε / 9 := by
  unfold scalarPathCosine cosine numerator rad
  norm_num
  have hs : (Real.sqrt 27) ^ 2 = (27 : ℝ) := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt (27 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  field_simp [ne_of_gt hspos]
  rw [hs]
  ring

/-- On the open path, clipping is inactive and the angle is the reflected arccosine. -/
theorem scalarPathAngle_eq (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    scalarPathAngle ε = Real.pi - Real.arccos (1 - ε / 9) := by
  rw [scalarPathAngle, scalarPathCosine_eq]
  have harg : -1 < -1 + ε / 9 ∧ -1 + ε / 9 < 1 := by constructor <;> linarith
  rw [min_eq_left (le_of_lt harg.2), max_eq_right (le_of_lt harg.1)]
  rw [show -1 + ε / 9 = -(1 - ε / 9) by ring, Real.arccos_neg]

theorem scalarPathAngle_zero : scalarPathAngle 0 = Real.pi := by
  rw [scalarPathAngle, scalarPathCosine_eq]
  norm_num [Real.arccos_neg_one]

/-- The arccosine cusp has the square-root lower bound forced by the cosine quadratic bound. -/
theorem arccos_cusp_lower_bound (ε : ℝ) (hε : 0 ≤ ε) (hε9 : ε ≤ 9) :
    Real.arccos (1 - ε / 9) ≥ Real.sqrt (2 * ε / 9) := by
  have harg : -1 ≤ 1 - ε / 9 ∧ 1 - ε / 9 ≤ 1 := by constructor <;> linarith
  let θ := Real.arccos (1 - ε / 9)
  have hθ : 0 ≤ θ := Real.arccos_nonneg _
  have hcos : Real.cos θ = 1 - ε / 9 := by
    dsimp [θ]
    exact Real.cos_arccos harg.1 harg.2
  have hquad := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hsq : 2 * ε / 9 ≤ θ ^ 2 := by
    nlinarith [hquad]
  have hsqrt : Real.sqrt (2 * ε / 9) ≤ Real.sqrt (θ ^ 2) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hθ] at hsqrt
  exact hsqrt

theorem scalarPathAngle_gap_lower_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    |scalarPathAngle ε - scalarPathAngle 0| ≥ Real.sqrt (2 * ε / 9) := by
  rw [scalarPathAngle_eq ε hε hε1, scalarPathAngle_zero]
  have hθ : 0 ≤ Real.arccos (1 - ε / 9) := Real.arccos_nonneg _
  rw [show (Real.pi - Real.arccos (1 - ε / 9)) - Real.pi =
      -(Real.arccos (1 - ε / 9)) by ring, abs_neg, abs_of_nonneg hθ]
  exact arccos_cusp_lower_bound ε (le_of_lt hε) (by linarith)

/-- Every finite linear bound against the parameter ε is defeated by the cusp. -/
theorem scalarPathAngle_not_parameter_lipschitz :
    ∀ K : ℝ, 0 ≤ K → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      Real.sqrt (2 * ε / 9) > K * (ε / Real.sqrt 255) := by
  intro K hK
  have hs255 : 0 < Real.sqrt (255 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  let δ := min (1 : ℝ) (510 / (9 * (K + 1) ^ 2))
  have hδ : 0 < δ := by
    dsimp [δ]
    apply lt_min (by norm_num)
    positivity
  refine ⟨δ / 2, by positivity, ?_, ?_⟩
  · dsimp [δ]
    have hmin : δ ≤ 1 := min_le_left _ _
    linarith
  have hδbound : δ ≤ 510 / (9 * (K + 1) ^ 2) := min_le_right _ _
  have hK1 : 0 < K + 1 := by linarith
  have hden : 0 < 9 * (K + 1) ^ 2 := by positivity
  have hsqrtε : 0 < Real.sqrt (2 * (δ / 2) / 9) := by positivity
  have hboundmul : 9 * (K + 1) ^ 2 * δ ≤ 510 := by
    calc
      9 * (K + 1) ^ 2 * δ = δ * (9 * (K + 1) ^ 2) := by ring
      _ ≤ 510 := (le_div_iff₀ hden).mp hδbound
  have hklt : K ^ 2 < (K + 1) ^ 2 := by nlinarith
  have hstrict : 9 * K ^ 2 * δ < 1020 := by
    have hstep : 9 * K ^ 2 * δ < 9 * (K + 1) ^ 2 * δ := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hklt (by norm_num)) hδ
    linarith
  have hsq : (K * ((δ / 2) / Real.sqrt 255)) ^ 2 <
      (Real.sqrt (2 * (δ / 2) / 9)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
    have hs255sq : (Real.sqrt (255 : ℝ)) ^ 2 = 255 := Real.sq_sqrt (by norm_num)
    field_simp [hs255.ne']
    nlinarith [hstrict, hs255sq]
  have hleft : 0 < Real.sqrt (2 * (δ / 2) / 9) := hsqrtε
  have hright : 0 ≤ K * ((δ / 2) / Real.sqrt 255) := by positivity
  nlinarith

theorem scalarPathAngle_gap_not_parameter_lipschitz :
    ∀ K : ℝ, 0 ≤ K → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      |scalarPathAngle ε - scalarPathAngle 0| > K * (ε / Real.sqrt 255) := by
  intro K hK
  obtain ⟨ε, hε, hε1, hbound⟩ := scalarPathAngle_not_parameter_lipschitz K hK
  refine ⟨ε, hε, hε1, ?_⟩
  exact lt_of_lt_of_le hbound (scalarPathAngle_gap_lower_bound ε hε hε1)

#print axioms scalarPathCosine_eq
#print axioms scalarPathAngle_eq
#print axioms arccos_cusp_lower_bound
#print axioms scalarPathAngle_not_parameter_lipschitz
#print axioms scalarPathAngle_gap_not_parameter_lipschitz

end D5.S3.Geometry.Hyperideal.ScalarAngleNonLipschitz
