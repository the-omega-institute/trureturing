/- GID: D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier
   generality: I
   mirror-B: D5/B/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The conjugate golden mode scales by minus the inverse golden ratio,
     while its ratio to the dominant mode scales by its inverse square. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.PrimeObserver.ProjectiveMemory.GoldenProjectiveMultiplier

open scoped goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap

/-- One modal step in the eigenbasis of the Fibonacci matrix. The first
coordinate is dominant and the second coordinate is stable. -/
def goldenModalStep (state : ℝ × ℝ) : ℝ × ℝ :=
  (Real.goldenRatio * state.1, Real.goldenConj * state.2)

/-- Stable coordinate divided by the dominant coordinate. -/
def projectiveDefect (state : ℝ × ℝ) : ℝ :=
  state.2 / state.1

/-- The ambient stable eigenvalue is minus the inverse golden ratio. -/
theorem golden_conjugate_eq_neg_inv :
    Real.goldenConj = -Real.goldenRatio⁻¹ := by
  rw [Real.inv_goldenRatio]
  ring

/-- The ratio of stable and dominant eigenvalues is the exact projective
completion multiplier. -/
theorem stable_dominant_ratio_eq_projective_multiplier :
    Real.goldenConj / Real.goldenRatio =
      goldenProjectiveMultiplier := by
  rw [div_eq_mul_inv, Real.inv_goldenRatio]
  unfold goldenProjectiveMultiplier
  rw [Real.inv_goldenRatio]
  ring

/-- One Fibonacci modal step multiplies the normalized defect by the
projective multiplier. -/
theorem projective_defect_modal_step {A D : ℝ} (hA : A ≠ 0) :
    projectiveDefect (goldenModalStep (A, D)) =
      goldenProjectiveMultiplier * projectiveDefect (A, D) := by
  have hPhi : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
  rw [projectiveDefect, goldenModalStep, projectiveDefect]
  change (Real.goldenConj * D) / (Real.goldenRatio * A) =
    goldenProjectiveMultiplier * (D / A)
  rw [← stable_dominant_ratio_eq_projective_multiplier]
  field_simp [hA, hPhi]

/-- Abstract recurrence form: ambient laws `A' = φA` and `D' = ψD` imply the
projective law whenever the dominant coordinate is nonzero. -/
theorem projective_multiplier_of_modal_laws
    {A D A' D' : ℝ} (hA : A ≠ 0)
    (hA' : A' = Real.goldenRatio * A)
    (hD' : D' = Real.goldenConj * D) :
    D' / A' = goldenProjectiveMultiplier * (D / A) := by
  subst A'
  subst D'
  exact projective_defect_modal_step hA

/-- Adding an explicit forcing term separates homogeneous golden contraction
from new layer-dependent information. -/
def forcedProjectiveStep (theta forcing : ℝ) : ℝ :=
  goldenProjectiveMultiplier * theta + forcing

@[simp]
theorem forced_projective_step_zero (theta : ℝ) :
    forcedProjectiveStep theta 0 =
      goldenProjectiveMultiplier * theta := by
  simp [forcedProjectiveStep]

/-- A vanishing state with zero forcing remains zero in one step. -/
theorem zero_state_zero_forcing (forcing : ℝ) (hForcing : forcing = 0) :
    forcedProjectiveStep 0 forcing = 0 := by
  simp [forcedProjectiveStep, hForcing]

/-- The ambient stable eigenvalue and projective multiplier encode different
normalization levels. -/
theorem ambient_and_projective_multipliers_ne :
    Real.goldenConj ≠ goldenProjectiveMultiplier := by
  intro h
  rw [golden_conjugate_eq_neg_inv] at h
  unfold goldenProjectiveMultiplier at h
  let a : ℝ := Real.goldenRatio⁻¹
  have haPos : 0 < a := inv_pos.mpr Real.goldenRatio_pos
  have haLt : a < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  change -a = -(a ^ 2) at h
  have hEq : a = a ^ 2 := by linarith
  nlinarith

#print axioms stable_dominant_ratio_eq_projective_multiplier
#print axioms projective_defect_modal_step
#print axioms projective_multiplier_of_modal_laws
#print axioms ambient_and_projective_multipliers_ne

end D5.S3.PrimeObserver.ProjectiveMemory.GoldenProjectiveMultiplier
