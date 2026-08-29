/- GID: D5/S3/Observer/WorldModel/FixedPointStabilityProfile
   generality: G
   mirror-B: D5/B/S3/Observer/WorldModel/FixedPointStabilityProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform fixed-point stability is a separate multiplier profile whose
     canonical golden projective radius is positive, strictly below one, and
     sharper than the ambient stable ratio. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative

/-!
Exact fixedness, bridge coherence, and local attraction are independent fields.
This module formalizes the attraction field as a uniform absolute-multiplier
bound.  A smaller admissible radius is a stronger contraction certificate.
The golden result is restricted to the canonical projective completion system;
it is not a claim that the golden ratio attracts under every self-map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.WorldModel.FixedPointStabilityProfile

open scoped goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
open D5.S3.CompletionDynamics.GoldenMobius.GoldenProjectiveDerivative

/-- A family of local multipliers is uniformly attracting with certified radius
`radius`. -/
def UniformRadiusBound {Index : Type*}
    (multiplier : Index → ℝ) (radius : ℝ) : Prop :=
  0 ≤ radius ∧ radius < 1 ∧ ∀ i, |multiplier i| ≤ radius

/-- Existence of some strict uniform contraction radius. -/
def IsUniformlyAttracting {Index : Type*}
    (multiplier : Index → ℝ) : Prop :=
  ∃ radius, UniformRadiusBound multiplier radius

/-- Every coordinate of a uniformly bounded profile is strictly attracting. -/
theorem uniform_radius_bound_each_attracting
    {Index : Type*} {multiplier : Index → ℝ} {radius : ℝ}
    (hBound : UniformRadiusBound multiplier radius) (i : Index) :
    |multiplier i| < 1 := by
  exact lt_of_le_of_lt (hBound.2.2 i) hBound.2.1

/-- Enlarging a valid radius below one preserves validity. -/
theorem uniform_radius_bound_mono
    {Index : Type*} {multiplier : Index → ℝ} {small large : ℝ}
    (hSmall : UniformRadiusBound multiplier small)
    (hLe : small ≤ large) (hLarge : large < 1) :
    UniformRadiusBound multiplier large := by
  refine ⟨le_trans hSmall.1 hLe, hLarge, ?_⟩
  intro i
  exact le_trans (hSmall.2.2 i) hLe

/-- Canonical absolute radius of golden projective completion. -/
def goldenProjectiveRadius : ℝ :=
  (Real.goldenRatio⁻¹) ^ 2

/-- The golden projective radius is positive. -/
theorem golden_projective_radius_pos :
    0 < goldenProjectiveRadius := by
  unfold goldenProjectiveRadius
  positivity

/-- The absolute golden completion multiplier is exactly its positive radius. -/
theorem abs_golden_multiplier_eq_radius :
    |goldenProjectiveMultiplier| = goldenProjectiveRadius := by
  exact abs_golden_projective_multiplier

/-- The canonical projective golden system is strictly attracting. -/
theorem golden_projective_radius_lt_one :
    goldenProjectiveRadius < 1 := by
  rw [← abs_golden_multiplier_eq_radius]
  exact abs_golden_projective_multiplier_lt_one

/-- Its multiplier is negative, recording the alternating side of approach. -/
theorem golden_projective_multiplier_neg :
    goldenProjectiveMultiplier < 0 := by
  unfold goldenProjectiveMultiplier
  have hPositive : 0 < (Real.goldenRatio⁻¹) ^ 2 := by
    positivity
  linarith

/-- Projective normalization contracts more strongly than the ambient stable
ratio `φ⁻¹`. -/
theorem golden_projective_radius_lt_ambient_radius :
    goldenProjectiveRadius < Real.goldenRatio⁻¹ := by
  let a : ℝ := Real.goldenRatio⁻¹
  have hPositive : 0 < a := by
    dsimp [a]
    exact inv_pos.mpr Real.goldenRatio_pos
  have hLessOne : a < 1 := by
    dsimp [a]
    exact inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  change a ^ 2 < a
  nlinarith

/-- A world-model family whose every local multiplier is the canonical golden
projective multiplier has the exact uniform radius `φ⁻²`. -/
theorem golden_constant_profile_uniform (Index : Type*) :
    UniformRadiusBound
      (fun _ : Index => goldenProjectiveMultiplier)
      goldenProjectiveRadius := by
  refine ⟨golden_projective_radius_pos.le,
    golden_projective_radius_lt_one, ?_⟩
  intro i
  rw [abs_golden_multiplier_eq_radius]

/-- The canonical golden constant profile is uniformly attracting. -/
theorem golden_constant_profile_is_uniformly_attracting (Index : Type*) :
    IsUniformlyAttracting
      (fun _ : Index => goldenProjectiveMultiplier) := by
  exact ⟨goldenProjectiveRadius, golden_constant_profile_uniform Index⟩

#print axioms uniform_radius_bound_each_attracting
#print axioms uniform_radius_bound_mono
#print axioms golden_projective_radius_pos
#print axioms abs_golden_multiplier_eq_radius
#print axioms golden_projective_radius_lt_one
#print axioms golden_projective_multiplier_neg
#print axioms golden_projective_radius_lt_ambient_radius
#print axioms golden_constant_profile_uniform
#print axioms golden_constant_profile_is_uniformly_attracting

end D5.S3.Observer.WorldModel.FixedPointStabilityProfile
