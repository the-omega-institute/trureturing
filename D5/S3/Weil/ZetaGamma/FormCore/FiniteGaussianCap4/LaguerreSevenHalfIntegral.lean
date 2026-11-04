/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfIntegral
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:fixed-alpha-laguerre-helper)
   anchors: []
   utility: none
   digest: Gamma-weighted integrals for the alpha seven halves Laguerre polynomials. -/
/-
Real Laguerre adaptation at alpha=7/2, 2026-10-26.
SPDX-License-Identifier: Apache-2.0

Modified/adapted polynomial-induction method from the OAI project, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/MathematicalPhysics/DefocusingNLS/Certificates/LaguerreIntegral.lean.
The alpha=0 complex integral is replaced by the real weighted alpha=7/2
integral. All Gamma parameters and powers are re-proved here. No OAI imports.
Applicable upstream license: LaguerreSevenHalfPolynomial.lean (Apache-2.0).
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfMoment
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option autoImplicit false

noncomputable section

open Polynomial MeasureTheory Set

namespace FiniteGaussianCap4.LaguerreSevenHalf

/-- Restoring the Gamma(9/2) factor in the normalized moments. -/
theorem Gamma_eq_momentWeight (n : ℕ) :
    Real.Gamma ((n : ℝ) + 9 / 2) = Real.Gamma (9 / 2) * momentWeight n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have he : ((n + 1 : ℕ) : ℝ) + 9 / 2 = ((n : ℝ) + 9 / 2) + 1 := by
        push_cast
        ring
      rw [he, Real.Gamma_add_one (by positivity), ih, momentWeight_succ]
      ring

private theorem weighted_monomial_eq (n : ℕ) (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) * x ^ (7 / 2 : ℝ) * x ^ n =
      Real.exp (-x) * x ^ (((n : ℝ) + 9 / 2) - 1) := by
  rw [show ((n : ℝ) + 9 / 2) - 1 = (7 / 2 : ℝ) + n by ring,
    Real.rpow_add hx, Real.rpow_natCast]
  ring

/-- Actual absolute integrability of each weighted monomial. -/
theorem integrable_weighted_monomial (n : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (7 / 2 : ℝ) * x ^ n)
      (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (n : ℝ) + 9 / 2) (by positivity)
  exact h.congr_fun (fun x hx => (weighted_monomial_eq n x hx).symm) measurableSet_Ioi

theorem integral_weighted_monomial (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (7 / 2 : ℝ) * x ^ n) =
      Real.Gamma (9 / 2) * momentWeight n := by
  calc
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (((n : ℝ) + 9 / 2) - 1) := by
      exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => weighted_monomial_eq n x hx)
    _ = Real.Gamma ((n : ℝ) + 9 / 2) :=
      (Real.Gamma_eq_integral (by positivity)).symm
    _ = Real.Gamma (9 / 2) * momentWeight n := Gamma_eq_momentWeight n

/-- The finite polynomial integral has its required L1 domain. -/
theorem integrable_weighted_polynomial (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (7 / 2 : ℝ) * p.eval x)
      (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert hp.add hq using 1
      funext x
      simp only [Polynomial.eval_add, mul_add, Pi.add_apply]
  | monomial n a =>
      change Integrable _ (volume.restrict (Ioi 0))
      convert (integrable_weighted_monomial n).const_mul a using 1
      funext x
      simp only [Polynomial.eval_monomial]
      ring

/-- Integral realization of the concrete finite Pochhammer moment map.
This is not an assumed orthogonality, expansion, or basis theorem. -/
theorem integral_weighted_polynomial (p : ℝ[X]) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (7 / 2 : ℝ) * p.eval x) =
      Real.Gamma (9 / 2) * moment p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add, mul_add]
      rw [integral_add (integrable_weighted_polynomial p)
        (integrable_weighted_polynomial q), hp, hq, map_add]
      ring
  | monomial n a =>
      simp only [Polynomial.eval_monomial, moment_monomial]
      calc
        _ = ∫ x in Ioi (0 : ℝ),
            a * (Real.exp (-x) * x ^ (7 / 2 : ℝ) * x ^ n) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          ring
        _ = a * (Real.Gamma (9 / 2) * momentWeight n) := by
          rw [integral_const_mul, integral_weighted_monomial]
        _ = Real.Gamma (9 / 2) * (momentWeight n * a) := by ring

/-- Genuine weighted orthogonality with the correct unnormalized norm. -/
theorem integral_weighted_laguerre_product (n m : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (7 / 2 : ℝ) *
      ((laguerre n).eval x * (laguerre m).eval x)) =
        if n = m then Real.Gamma ((n : ℝ) + 9 / 2) / (n.factorial : ℝ) else 0 := by
  simp_rw [← Polynomial.eval_mul]
  rw [integral_weighted_polynomial, moment_product]
  split_ifs
  · rw [Gamma_eq_momentWeight]
    ring
  · simp

end FiniteGaussianCap4.LaguerreSevenHalf
