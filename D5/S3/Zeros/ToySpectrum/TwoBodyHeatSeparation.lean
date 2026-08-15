/- GID: D5/S3/Zeros/ToySpectrum/TwoBodyHeatSeparation
   generality: I
   mirror-B: D5/B/S3/Zeros/ToySpectrum/TwoBodyHeatSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The split quadratic heat roots have squared gap 8t - 4c0. -/

import D5.S3.Zeros.ToySpectrum.QuadraticCollisionModel

namespace D5.S3.Zeros.ToySpectrum.TwoBodyHeatSeparation

open QuadraticCollisionModel
open Polynomial

/-- The two-body heat polynomial is the collision model with linearly shifted parameter. -/
noncomputable def twoBodyHeatPolynomial (c₀ t : ℝ) : ℂ[X] :=
  quadraticCollisionPolynomial (c₀ - 2 * t)

/-- After the collision time, the two real roots are distinct and their squared gap is linear. -/
theorem two_body_heat_real_root_separation (c₀ t : ℝ) (ht : c₀ / 2 < t) :
    (twoBodyHeatPolynomial c₀ t).roots =
        {((Real.sqrt (2 * t - c₀) : ℝ) : ℂ), -((Real.sqrt (2 * t - c₀) : ℝ) : ℂ)} ∧
      ((Real.sqrt (2 * t - c₀) : ℝ) : ℂ) ≠ -((Real.sqrt (2 * t - c₀) : ℝ) : ℂ) ∧
      (Real.sqrt (2 * t - c₀) - -Real.sqrt (2 * t - c₀)) ^ 2 = 8 * t - 4 * c₀ := by
  have hnegative : c₀ - 2 * t < 0 := by linarith
  have hparameter : -(c₀ - 2 * t) = 2 * t - c₀ := by ring
  have hcertificate :=
    (quadratic_collision_model_certificate (c₀ - 2 * t)).1 hnegative
  have hnonnegative : 0 ≤ 2 * t - c₀ := by linarith
  have hsqrt : Real.sqrt (2 * t - c₀) ^ 2 = 2 * t - c₀ :=
    Real.sq_sqrt hnonnegative
  refine ⟨?_, ?_, ?_⟩
  · simpa [twoBodyHeatPolynomial, hparameter] using hcertificate.1
  · simpa [hparameter] using hcertificate.2
  · nlinarith

end D5.S3.Zeros.ToySpectrum.TwoBodyHeatSeparation
