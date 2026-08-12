/- GID: D5/S3/Fourier/GaussianThetaTransformation
   generality: G
   mirror-B: D5/B/S3/Fourier/GaussianThetaTransformation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The positive-real Gaussian theta sum transforms by reciprocal scaling. -/

import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

namespace D5.S3.Fourier.GaussianThetaTransformation

/-- For every positive real parameter, the integer-indexed Gaussian theta sum at `t` is the
reciprocal square-root scaling of the same sum at `t⁻¹`. This is a thin wrapper around the
corresponding pinned Mathlib Poisson-summation theorem. -/
theorem gaussian_theta_transformation (t : ℝ) (ht : 0 < t) :
    (∑' n : ℤ, Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) =
      t ^ (-(1 / 2) : ℝ) *
        ∑' n : ℤ, Real.exp (-Real.pi * t⁻¹ * (n : ℝ) ^ 2) := by
  rw [Real.tsum_exp_neg_mul_int_sq ht]
  rw [Real.rpow_neg (le_of_lt ht), one_div]
  congr 2

end D5.S3.Fourier.GaussianThetaTransformation
