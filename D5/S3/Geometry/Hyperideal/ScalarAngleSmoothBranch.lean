/- GID: D5/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/ScalarAngleSmoothBranch
   mirror-E: none(waiver:scalar-angle-smooth-branch)
   anchors: []
   utility: none
   digest: The raw scalar cosine branch is smooth while its clipped angle has an endpoint cusp. -/

import D5.S3.Geometry.Hyperideal.ScalarAngleNonLipschitz
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Geometry.Hyperideal.ScalarAngleSmoothBranch

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open D5.S3.Geometry.Hyperideal.ScalarAngleNonLipschitz

/-- The raw first-slot cosine along the length parameter s. -/
def scalarLengthRawCosine (s : ℝ) : ℝ :=
  cosine 2 2 2 (Real.cosh s) 2 2

theorem scalarLengthRawCosine_eq (s : ℝ) :
    scalarLengthRawCosine s = (8 - Real.cosh s) / 9 := by
  unfold scalarLengthRawCosine cosine numerator rad
  norm_num
  have hs : (Real.sqrt 27) ^ 2 = (27 : ℝ) := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt (27 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  field_simp [ne_of_gt hspos]
  rw [hs]
  ring

theorem scalarLengthRawCosine_differentiable :
    Differentiable ℝ scalarLengthRawCosine := by
  rw [show scalarLengthRawCosine = (fun s : ℝ => (8 - Real.cosh s) / 9) by
    funext s; exact scalarLengthRawCosine_eq s]
  fun_prop

theorem smooth_raw_branch_but_angle_not_parameter_lipschitz :
    Differentiable ℝ scalarLengthRawCosine ∧
      ∀ K : ℝ, 0 ≤ K → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        |scalarPathAngle ε - scalarPathAngle 0| > K * (ε / Real.sqrt 255) := by
  exact ⟨scalarLengthRawCosine_differentiable,
    scalarPathAngle_gap_not_parameter_lipschitz⟩

#print axioms scalarLengthRawCosine_eq
#print axioms scalarLengthRawCosine_differentiable
#print axioms smooth_raw_branch_but_angle_not_parameter_lipschitz

end D5.S3.Geometry.Hyperideal.ScalarAngleSmoothBranch
