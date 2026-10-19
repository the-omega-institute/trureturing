/- GID: D5/S3/Quantum/Subentropy/GaussianRepresentation
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/GaussianRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Probability.Distributions.Gaussian.Real]
   utility: none
   digest: Exact Laplace transforms of finite diagonal complex Gaussian quadratic forms. -/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-! Independent real coordinate pairs supply the complex Gaussian Laplace transform. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace D5.S3.Quantum.Subentropy.GaussianRepresentation

private theorem real_gaussian_laplace (c : ℝ) (hc : 0 ≤ c) :
    (∫ x : ℝ, Real.exp (-c * x^2 / 2) ∂gaussianReal 0 1)^2 = 1 / (1 + c) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have heq : (fun x : ℝ => gaussianPDFReal 0 1 x • Real.exp (-c * x^2 / 2)) =
      fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1+c)/2) * x^2) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq, integral_const_mul, integral_gaussian, mul_pow, inv_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi),
    Real.sq_sqrt (by positivity : 0 ≤ Real.pi / ((1+c)/2))]
  have hp := Real.pi_pos
  have hc1 : 1+c ≠ 0 := by positivity
  field_simp

/-- The Laplace transform of a diagonal quadratic form in independent pairs of
standard real Gaussian coordinates. Each pair is one standard complex coordinate. -/
theorem diagonal_gaussian_laplace {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s : ℝ) (hs : 0 ≤ s) :
    (∫ z : (ι × Fin 2) → ℝ,
      Real.exp (∑ j, -(s * p j.1) * (z j)^2 / 2)
        ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) =
      ∏ i, (1 + s * p i)⁻¹ := by
  classical
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (fun j : ι × Fin 2 => fun x : ℝ => Real.exp (-(s * p j.1) * x^2 / 2))]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.prod_univ_two]
  rw [← sq]
  simpa [one_div] using real_gaussian_laplace (s * p i) (mul_nonneg hs (hp i))

end D5.S3.Quantum.Subentropy.GaussianRepresentation
