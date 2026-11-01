/- GID: D5/S3/VertexAlgebra/TwistedGround/GaussianCoefficientContinuity
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/GaussianCoefficientContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuity of actual finite Gaussian coefficients in all kernel entries. -/

import D5.S3.VertexAlgebra.TwistedGround.FactorialFockQuadraticEstimate

/-! Fixed Gaussian occupations depend continuously on the finite kernel entries. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientContinuity
open MvPolynomial FactorialFockQuadraticEstimate
universe u
variable {J : Type u} [Fintype J] [DecidableEq J]

private theorem quadratic_coeff_continuous (d : J →₀ ℕ) :
    Continuous (fun K : Matrix J J ℂ => (quadratic K).coeff d) := by
  simp only [quadratic, coeff_smul, coeff_sum, smul_eq_mul]
  fun_prop

private theorem power_coeff_continuous (n : ℕ) (d : J →₀ ℕ) :
    Continuous (fun K : Matrix J J ℂ => (quadratic K ^ n).coeff d) := by
  induction n generalizing d with
  | zero =>
    simpa only [pow_zero] using
      (continuous_const : Continuous (fun _ : Matrix J J ℂ =>
        (1 : MvPolynomial J ℂ).coeff d))
  | succ n ih =>
    simp only [pow_succ, coeff_mul]
    apply continuous_finset_sum
    intro a ha
    exact (ih a.1).mul (quadratic_coeff_continuous a.2)

/-- Every fixed ordinary coefficient is a finite polynomial in the kernel
entries; no norm or smallness hypothesis on the effective kernel is needed. -/
theorem coefficient_continuous (d : J →₀ ℕ) :
    Continuous (fun K : Matrix J J ℂ => gaussianCoefficient K d) := by
  simp only [gaussianCoefficient, gaussianPiece, coeff_smul, smul_eq_mul]
  exact continuous_const.mul (power_coeff_continuous _ d)

end D5.S3.VertexAlgebra.TwistedGround.GaussianCoefficientContinuity
