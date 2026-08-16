/- GID: D5/S3/PrimeForms/GaussianIntegers/GaussianIntegerNorm
   generality: G
   mirror-B: D5/B/S3/PrimeForms/GaussianIntegers/GaussianIntegerNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A Gaussian integer times its complex conjugate is its sum-of-two-squares norm. -/

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

open scoped ComplexConjugate

namespace D5.S3.PrimeForms.GaussianIntegers.GaussianIntegerNorm

/-- A Gaussian integer `a + bI` times its complex conjugate has norm `a² + b²`. -/
theorem gaussian_integer_mul_conj_eq_sq_add_sq (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * Complex.I) *
      conj ((a : ℂ) + (b : ℂ) * Complex.I) =
        ((a ^ 2 + b ^ 2 : ℤ) : ℂ) := by
  rw [Complex.mul_conj]
  norm_num [Complex.normSq_apply, pow_two]

#print axioms gaussian_integer_mul_conj_eq_sq_add_sq

end D5.S3.PrimeForms.GaussianIntegers.GaussianIntegerNorm
