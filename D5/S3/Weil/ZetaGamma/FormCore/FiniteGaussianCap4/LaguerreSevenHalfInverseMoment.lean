/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfInverseMoment
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: The exact inverse weighted norm of every actual normalized Laguerre mode. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfCentralNormalization
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The inverse weighted norm is derived from convergent Gamma integrals and
actual Laguerre orthogonality. Polynomial induction proves the exact weighted
integration-by-parts identity; there are no boundary or integrability premises.
The imported polynomial and moment proofs retain their OAI attribution and
Apache-2.0 license. The inverse-moment step is proved here from those imported identities. -/

set_option autoImplicit false
noncomputable section
open Polynomial MeasureTheory Set

namespace FiniteGaussianCap4.LaguerreSevenHalf

private theorem gamma_monomial_density (s : ℝ) (j : ℕ) (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) * x ^ s * x ^ j =
      Real.exp (-x) * x ^ ((s + j + 1) - 1) := by
  rw [show (s + (j : ℝ) + 1) - 1 = s + j by ring,
    Real.rpow_add hx, Real.rpow_natCast]
  ring

private theorem integrable_gamma_monomial (s : ℝ) (hs : -1 < s) (j : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ s * x ^ j) (Ioi 0) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  exact (Real.GammaIntegral_convergent (s := s + j + 1) (by linarith)).congr_fun
    (fun x hx => (gamma_monomial_density s j x hx).symm) measurableSet_Ioi

private theorem integral_gamma_monomial (s : ℝ) (hs : -1 < s) (j : ℕ) (a : ℝ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ s * (monomial j a).eval x) =
      a * Real.Gamma (s + j + 1) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc
    _ = ∫ x in Ioi (0 : ℝ), a *
        (Real.exp (-x) * x ^ ((s + j + 1) - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [Polynomial.eval_monomial, ← gamma_monomial_density s j x hx]
      ring
    _ = _ := by
      rw [integral_const_mul, ← Real.Gamma_eq_integral (by linarith : 0 < s + j + 1)]

private theorem integrable_gamma_polynomial (s : ℝ) (hs : -1 < s) (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ s * p.eval x) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert hp.add hq using 1
      funext x
      simp only [Polynomial.eval_add, mul_add, Pi.add_apply]
  | monomial j a =>
      change Integrable _ (volume.restrict (Ioi 0))
      convert (integrable_gamma_monomial s hs j).const_mul a using 1
      funext x
      simp only [Polynomial.eval_monomial]
      ring

/-- Exact zero-boundary Gamma integration by parts for every real polynomial.
Its proof evaluates all monomial integrals, including both endpoint domains,
and uses the proved Gamma recurrence rather than assuming any boundary law. -/
private theorem integral_gamma_polynomial_ibp (s : ℝ) (hs : 0 < s) (p : ℝ[X]) :
    s * (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (s - 1) * p.eval x) +
      (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ s * p.derivative.eval x) =
      ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ s * p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.derivative_add, Polynomial.eval_add, mul_add]
      rw [integral_add (integrable_gamma_polynomial (s - 1) (by linarith) p)
        (integrable_gamma_polynomial (s - 1) (by linarith) q),
        integral_add (integrable_gamma_polynomial s (by linarith) p.derivative)
        (integrable_gamma_polynomial s (by linarith) q.derivative),
        integral_add (integrable_gamma_polynomial s (by linarith) p)
        (integrable_gamma_polynomial s (by linarith) q)]
      linear_combination hp + hq
  | monomial j a =>
      cases j with
      | zero =>
          rw [integral_gamma_monomial (s - 1) (by linarith) 0 a,
            integral_gamma_monomial s (by linarith) 0 a]
          simp only [Polynomial.monomial_zero_left, Polynomial.derivative_C,
            Polynomial.eval_zero, mul_zero, integral_zero, add_zero, Nat.cast_zero]
          rw [show s - 1 + 1 = s by ring, Real.Gamma_add_one hs.ne']
          ring
      | succ j =>
          rw [Polynomial.derivative_monomial_succ,
            integral_gamma_monomial (s - 1) (by linarith) (j + 1) a,
            integral_gamma_monomial s (by linarith) j (a * (j + 1)),
            integral_gamma_monomial s (by linarith) (j + 1) a]
          push_cast
          rw [show s - 1 + ((j : ℝ) + 1) + 1 = s + j + 1 by ring,
            show s + ((j : ℝ) + 1) + 1 = (s + j + 1) + 1 by ring,
            Real.Gamma_add_one (by positivity : s + (j : ℝ) + 1 ≠ 0)]
          ring

private theorem moment_derivative_laguerre_square (n : ℕ) :
    moment (laguerre n * laguerre n).derivative = 0 := by
  have hder : ∀ m : ℕ, m ≤ n → moment ((laguerre m).derivative * laguerre n) = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro hm
        rw [derivative_step, sub_mul, map_sub, ih (by omega),
          moment_orthogonal m n (by omega), sub_self]
  rw [Polynomial.derivative_mul, map_add,
    mul_comm (laguerre n) (laguerre n).derivative,
    hder n le_rfl, add_zero]

private theorem integral_inverse_laguerre_square (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (5 / 2 : ℝ) *
      (laguerre n * laguerre n).eval x) =
      (2 / 7 : ℝ) * Real.Gamma ((n : ℝ) + 9 / 2) / (n.factorial : ℝ) := by
  have h := integral_gamma_polynomial_ibp (7 / 2) (by norm_num) (laguerre n * laguerre n)
  norm_num only [show (7 / 2 : ℝ) - 1 = 5 / 2 by norm_num] at h
  rw [integral_weighted_polynomial, integral_weighted_polynomial,
    moment_derivative_laguerre_square, mul_zero, add_zero, moment_norm,
    ← mul_div_assoc, ← Gamma_eq_momentWeight] at h
  linear_combination (2 / 7 : ℝ) * h

private theorem inverse_centralPsi_density (n : ℕ) (x : ℝ) (hx : 0 < x) :
    x ^ (5 / 2 : ℝ) * centralPsi x n ^ 2 =
      (centralNormalization n ^ 2 / (2 : ℝ) ^ (5 / 2 : ℝ)) *
        (Real.exp (-(2 * x)) * (2 * x) ^ (5 / 2 : ℝ) *
          (laguerre n * laguerre n).eval (2 * x)) := by
  have he : Real.exp (-x) ^ 2 = Real.exp (-(2 * x)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [centralPsi, phi, mul_pow, Polynomial.eval_mul,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le]
  rw [he]
  field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (5 / 2)).ne']

/-- Every actual normalized mode belongs to the inverse weighted L2 domain. -/
theorem centralPsi_integrable_inverse_square (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (5 / 2 : ℝ) * centralPsi x n ^ 2) (Ioi 0) := by
  have hg := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => Real.exp (-x) * x ^ (5 / 2 : ℝ) *
      (laguerre n * laguerre n).eval x) 0 (by norm_num : (0 : ℝ) < 2)).2
    (by
      simpa only [mul_zero] using
        (integrable_gamma_polynomial (5 / 2) (by norm_num)
          (laguerre n * laguerre n)))
  have hscaled : IntegrableOn (fun x : ℝ =>
      (centralNormalization n ^ 2 / (2 : ℝ) ^ (5 / 2 : ℝ)) *
        (Real.exp (-(2 * x)) * (2 * x) ^ (5 / 2 : ℝ) *
          (laguerre n * laguerre n).eval (2 * x))) (Ioi 0) :=
    hg.const_mul (centralNormalization n ^ 2 / (2 : ℝ) ^ (5 / 2 : ℝ))
  exact hscaled.congr_fun
    (fun x hx => (inverse_centralPsi_density n x hx).symm) measurableSet_Ioi

/-- The same inverse weighted norm is exactly 4/7 for every actual mode.
There is no finite cutoff, asymptotic approximation, or orthogonality premise. -/
theorem centralPsi_integral_inverse_square (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ (5 / 2 : ℝ) * centralPsi x n ^ 2) = (4 / 7 : ℝ) := by
  calc
    _ = ∫ x in Ioi (0 : ℝ),
        (centralNormalization n ^ 2 / (2 : ℝ) ^ (5 / 2 : ℝ)) *
          (Real.exp (-(2 * x)) * (2 * x) ^ (5 / 2 : ℝ) *
            (laguerre n * laguerre n).eval (2 * x)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => inverse_centralPsi_density n x hx)
    _ = (centralNormalization n ^ 2 / (2 : ℝ) ^ (5 / 2 : ℝ)) *
        ((2 : ℝ)⁻¹ * ((2 / 7 : ℝ) * Real.Gamma ((n : ℝ) + 9 / 2) /
          (n.factorial : ℝ))) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi
        (fun y : ℝ => Real.exp (-y) * y ^ (5 / 2 : ℝ) *
          (laguerre n * laguerre n).eval y) 0 (by norm_num : (0 : ℝ) < 2)]
      simp only [mul_zero, smul_eq_mul, integral_inverse_laguerre_square]
    _ = (4 / 7 : ℝ) := by
      have hp : (2 : ℝ) ^ (9 / 2 : ℝ) = (2 : ℝ) ^ (5 / 2 : ℝ) * 4 := by
        rw [show (9 / 2 : ℝ) = 5 / 2 + 2 by norm_num,
          Real.rpow_add (by norm_num), Real.rpow_two]
        norm_num
      rw [centralNormalization_sq, hp]
      field_simp [(Real.Gamma_pos_of_pos (show 0 < (n : ℝ) + 9 / 2 by positivity)).ne',
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (5 / 2)).ne',
        show (n.factorial : ℝ) ≠ 0 by positivity]

end FiniteGaussianCap4.LaguerreSevenHalf
