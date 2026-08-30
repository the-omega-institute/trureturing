/- GID: D5/S3/Observer/WorldModel/GoldenRealizationCertificate
   generality: I
   mirror-B: D5/B/S3/Observer/WorldModel/GoldenRealizationCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One certificate packages the quadratic, Fibonacci, rotation-trace, Mobius-fixed, and projective-attraction realizations of the golden structure while exhibiting a repelling countermodel. -/

import D5.S3.Observer.GoldenCoding.GoldenAngleTraceBridge
import D5.S3.Observer.WorldModel.FixedPointStabilityProfile
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
The certificate records a cross-representation structure.  It does not identify
all carriers as the same type, and it does not assert attraction for arbitrary
self-maps fixing the golden ratio.  The final affine countermodel proves that
fixedness and attraction are logically separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.WorldModel.GoldenRealizationCertificate

open scoped goldenRatio
open D5.S3.CompletionDynamics.GoldenMobius.GoldenMobiusMap
open D5.S3.Observer.GoldenCoding.GoldenAngleTraceBridge
open D5.S3.Observer.WorldModel.FixedPointStabilityProfile

/-- A typed package of the principal canonical golden realizations used by the
observer-completion theory. -/
structure GoldenCrossRepresentationCertificate : Prop where
  quadratic : Real.goldenRatio ^ 2 = Real.goldenRatio + 1
  reciprocalFixed : goldenMobius Real.goldenRatio = Real.goldenRatio
  angleTrace : rotationTrace goldenAngle = Real.goldenRatio
  fibonacciRecurrence : ∀ n : ℕ,
    Real.goldenRatio ^ (n + 2) =
      Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n
  multiplierRadius :
    |goldenProjectiveMultiplier| = goldenProjectiveRadius
  projectiveAttraction : goldenProjectiveRadius < 1

/-- The canonical golden structure satisfies the full cross-representation
certificate. -/
theorem canonical_golden_cross_representation_certificate :
    GoldenCrossRepresentationCertificate := by
  refine ⟨Real.goldenRatio_sq, golden_mobius_fixed_golden,
    golden_angle_trace_eq_golden_ratio, ?_,
    abs_golden_multiplier_eq_radius, golden_projective_radius_lt_one⟩
  intro n
  linarith [Real.goldenRatio_pow_sub_goldenRatio_pow n]

/-- An affine self-map fixing the golden point with repelling multiplier
`φ²`. -/
def goldenRepellingAffine (x : ℝ) : ℝ :=
  Real.goldenRatio + Real.goldenRatio ^ 2 * (x - Real.goldenRatio)

/-- The same golden point can be fixed in a different dynamical system. -/
theorem golden_repelling_affine_fixed :
    Function.IsFixedPt goldenRepellingAffine Real.goldenRatio := by
  simp [Function.IsFixedPt, goldenRepellingAffine]

/-- The affine countermodel has derivative `φ²` at the fixed point. -/
theorem golden_repelling_affine_hasDerivAt :
    HasDerivAt goldenRepellingAffine (Real.goldenRatio ^ 2)
      Real.goldenRatio := by
  have hSub :
      HasDerivAt (fun x : ℝ => x - Real.goldenRatio) 1
        Real.goldenRatio := by
    simpa using (hasDerivAt_id Real.goldenRatio).sub_const
      Real.goldenRatio
  have hScaled := hSub.const_mul (Real.goldenRatio ^ 2)
  have hScaled' :
      HasDerivAt
        (fun x : ℝ => Real.goldenRatio ^ 2 * (x - Real.goldenRatio))
        (Real.goldenRatio ^ 2) Real.goldenRatio := by
    apply hScaled.congr_deriv
    ring
  have hAffine := hScaled'.const_add Real.goldenRatio
  unfold goldenRepellingAffine
  exact hAffine

/-- The affine countermodel is strictly repelling. -/
theorem golden_repelling_affine_multiplier_gt_one :
    1 < |Real.goldenRatio ^ 2| := by
  rw [abs_of_pos]
  · nlinarith [Real.one_lt_goldenRatio]
  · positivity

/-- Hence fixedness of the golden point alone does not imply attraction. -/
theorem golden_fixed_does_not_force_attraction :
    Function.IsFixedPt goldenRepellingAffine Real.goldenRatio ∧
      1 < |Real.goldenRatio ^ 2| :=
  ⟨golden_repelling_affine_fixed,
    golden_repelling_affine_multiplier_gt_one⟩

#print axioms canonical_golden_cross_representation_certificate
#print axioms golden_repelling_affine_fixed
#print axioms golden_repelling_affine_hasDerivAt
#print axioms golden_repelling_affine_multiplier_gt_one
#print axioms golden_fixed_does_not_force_attraction

end D5.S3.Observer.WorldModel.GoldenRealizationCertificate
