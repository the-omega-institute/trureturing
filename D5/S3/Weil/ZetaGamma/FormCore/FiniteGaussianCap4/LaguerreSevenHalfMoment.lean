/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfMoment
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:fixed-alpha-laguerre-helper)
   anchors: []
   utility: none
   digest: Exact normalized moments and orthogonality at alpha seven halves. -/
/-
Real Laguerre adaptation at alpha=7/2, 2026-10-26.
SPDX-License-Identifier: Apache-2.0

Modified/adapted finite-moment/Green-identity proof method from the OAI project,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/MathematicalPhysics/DefocusingNLS/Certificates/LaguerreOrthogonality.lean.
The alpha=0 factorial moments and boundary identity are replaced by the actual
alpha=7/2 Pochhammer moments and zero-boundary weighted IBP identity. The norm
argument is new here, since the alpha=0 norm value does not match this parameter.
Applicable upstream license: LaguerreSevenHalfPolynomial.lean (Apache-2.0).
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfPolynomial
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped BigOperators

namespace FiniteGaussianCap4.LaguerreSevenHalf

/-- `M(p) = sum_j p_j (9/2)_j`. It is a concrete linear map, not an integral
or orthogonality assumption. Integral realization is a separate theorem. -/
def moment : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun j => momentWeight j • LinearMap.id

@[simp] theorem moment_monomial (j : ℕ) (a : ℝ) :
    moment (monomial j a) = momentWeight j * a := by
  simp [moment, Polynomial.lsum]

theorem moment_eq_sum (p : ℝ[X]) :
    moment p = ∑ j ∈ p.support, p.coeff j * momentWeight j := by
  simp [moment, Polynomial.lsum, Polynomial.sum_def, mul_comm]

@[simp] theorem moment_C (a : ℝ) : moment (C a) = a := by
  simpa using moment_monomial 0 a

@[simp] theorem moment_C_mul (a : ℝ) (p : ℝ[X]) :
    moment (C a * p) = a * moment p := by
  rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

/-- Algebraic weighted integration by parts. It is valid for every polynomial
and has no boundary evaluation term because the weight is x^(7/2) exp(-x). -/
theorem moment_ibp (p : ℝ[X]) :
    moment (X * p.derivative + (C (9 / 2 : ℝ) - X) * p) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have he : X * (p + q).derivative + (C (9 / 2 : ℝ) - X) * (p + q) =
          (X * p.derivative + (C (9 / 2 : ℝ) - X) * p) +
            (X * q.derivative + (C (9 / 2 : ℝ) - X) * q) := by
        rw [Polynomial.derivative_add]
        ring
      rw [he, map_add, hp, hq, add_zero]
  | monomial j a =>
      cases j with
      | zero =>
          simp only [Polynomial.monomial_zero_left, Polynomial.derivative_C,
            mul_zero, zero_add, sub_mul, map_sub, moment_C_mul]
          rw [Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial, moment_monomial]
          simp [momentWeight_succ]
          <;> ring
      | succ j =>
          simp only [Polynomial.derivative_monomial_succ, sub_mul, map_add,
            map_sub, Polynomial.X_mul_monomial, moment_monomial, moment_C_mul,
            momentWeight_succ]
          push_cast
          ring

/-- The alpha=7/2 Laguerre differential operator. -/
def operator (p : ℝ[X]) : ℝ[X] :=
  X * p.derivative.derivative + (C (9 / 2 : ℝ) - X) * p.derivative

/-- Green identity in its Dirichlet form, obtained by applying weighted IBP
only to the polynomial p' q. No analytic domain assumption is used. -/
theorem moment_green_derivative (p q : ℝ[X]) :
    moment (operator p * q) = -moment (X * (p.derivative * q.derivative)) := by
  have h := moment_ibp (p.derivative * q)
  have he : X * (p.derivative * q).derivative +
      (C (9 / 2 : ℝ) - X) * (p.derivative * q) =
        operator p * q + X * (p.derivative * q.derivative) := by
    simp only [operator, Polynomial.derivative_mul]
    ring
  rw [he, map_add] at h
  linear_combination h

/-- Symmetry for the actual normalized weighted moment. -/
theorem moment_green (p q : ℝ[X]) :
    moment (operator p * q) = moment (p * operator q) := by
  rw [moment_green_derivative]
  rw [mul_comm p (operator q), moment_green_derivative]
  congr 2
  ring

theorem operator_laguerre (n : ℕ) :
    operator (laguerre n) = -C (n : ℝ) * laguerre n := by
  have h := differential_equation n
  dsimp [operator]
  linear_combination h

/-- Pairwise orthogonality follows from distinct, proven ODE eigenvalues. -/
theorem moment_orthogonal (n m : ℕ) (hnm : n ≠ m) :
    moment (laguerre n * laguerre m) = 0 := by
  have hn := moment_green_derivative (laguerre n) (laguerre m)
  have hm := moment_green_derivative (laguerre m) (laguerre n)
  rw [operator_laguerre] at hn hm
  simp only [neg_mul, mul_assoc, map_neg, moment_C_mul] at hn hm
  rw [mul_comm (laguerre m) (laguerre n)] at hm
  have he : X * ((laguerre m).derivative * (laguerre n).derivative) =
      X * ((laguerre n).derivative * (laguerre m).derivative) := by ring
  rw [he] at hm
  have hz : ((n : ℝ) - m) * moment (laguerre n * laguerre m) = 0 := by
    linear_combination hm - hn
  exact (mul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr (by exact_mod_cast hnm))

/-- The weighted derivative energy is fixed by the ODE. -/
theorem moment_gradient_self (n : ℕ) :
    moment (X * ((laguerre n).derivative * (laguerre n).derivative)) =
      (n : ℝ) * moment (laguerre n * laguerre n) := by
  have h := moment_green_derivative (laguerre n) (laguerre n)
  rw [operator_laguerre] at h
  simp only [neg_mul, mul_assoc, map_neg, moment_C_mul] at h
  linear_combination h

/-- The mixed weighted derivative moment is derived from the consecutive
orthogonality identity and the proven derivative step. -/
theorem moment_X_derivative_self (n : ℕ) :
    moment (X * ((laguerre n).derivative * laguerre n)) =
      (n : ℝ) * moment (laguerre n * laguerre n) := by
  have h := moment_green_derivative (laguerre (n + 1)) (laguerre n)
  rw [operator_laguerre] at h
  simp only [neg_mul, mul_assoc, map_neg, moment_C_mul,
    moment_orthogonal (n + 1) n (by omega), mul_zero] at h
  have he : X * ((laguerre (n + 1)).derivative * (laguerre n).derivative) =
      X * ((laguerre n).derivative * (laguerre n).derivative) -
        X * ((laguerre n).derivative * laguerre n) := by
    rw [derivative_step]
    ring
  rw [he, map_sub, moment_gradient_self] at h
  linear_combination -h

/-- The diagonal of multiplication by X, derived before any norm evaluation. -/
theorem moment_X_self (n : ℕ) :
    moment (X * (laguerre n * laguerre n)) =
      (2 * (n : ℝ) + 9 / 2) * moment (laguerre n * laguerre n) := by
  have h := moment_ibp (laguerre n * laguerre n)
  have he : X * (laguerre n * laguerre n).derivative +
      (C (9 / 2 : ℝ) - X) * (laguerre n * laguerre n) =
        C (2 : ℝ) * (X * ((laguerre n).derivative * laguerre n)) +
          C (9 / 2 : ℝ) * (laguerre n * laguerre n) -
            X * (laguerre n * laguerre n) := by
    rw [Polynomial.derivative_mul, Polynomial.C_ofNat]
    ring
  rw [he, map_sub, map_add, moment_C_mul, moment_C_mul,
    moment_X_derivative_self] at h
  linear_combination -h

/-- Genuine norm recurrence; in particular the normalization is not supplied
as a theorem hypothesis. -/
theorem moment_norm_step (n : ℕ) :
    ((n : ℝ) + 1) * moment (laguerre (n + 1) * laguerre (n + 1)) =
      ((n : ℝ) + 9 / 2) * moment (laguerre n * laguerre n) := by
  have h := moment_green_derivative (laguerre (n + 1)) (laguerre (n + 1))
  rw [operator_laguerre] at h
  simp only [neg_mul, mul_assoc, map_neg, moment_C_mul, Nat.cast_add,
    Nat.cast_one] at h
  have he : X * ((laguerre (n + 1)).derivative * (laguerre (n + 1)).derivative) =
      X * ((laguerre n).derivative * (laguerre n).derivative) -
        C (2 : ℝ) * (X * ((laguerre n).derivative * laguerre n)) +
          X * (laguerre n * laguerre n) := by
    rw [derivative_step, Polynomial.C_ofNat]
    ring
  rw [he, map_add, map_sub, moment_C_mul, moment_gradient_self,
    moment_X_derivative_self, moment_X_self] at h
  linear_combination -h

/-- Normalized squared norm `(9/2)_n/n!`. -/
theorem moment_norm (n : ℕ) :
    moment (laguerre n * laguerre n) = momentWeight n / (n.factorial : ℝ) := by
  induction n with
  | zero =>
      simpa only [laguerre_zero, mul_one, momentWeight_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, Polynomial.C_1] using (moment_C (1 : ℝ))
  | succ n ih =>
      have h := moment_norm_step n
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      calc
        _ = (((n : ℝ) + 9 / 2) * moment (laguerre n * laguerre n)) /
            ((n : ℝ) + 1) := by
          apply (eq_div_iff hn).2
          simpa only [mul_comm] using h
        _ = momentWeight (n + 1) / ((n + 1).factorial : ℝ) := by
          rw [ih, momentWeight_succ, Nat.factorial_succ]
          push_cast
          field_simp [hn, show (n.factorial : ℝ) ≠ 0 by positivity]
          <;> ring

/-- Both branches are computed, not assumed. -/
theorem moment_product (n m : ℕ) :
    moment (laguerre n * laguerre m) =
      if n = m then momentWeight n / (n.factorial : ℝ) else 0 := by
  split_ifs with h
  · subst m
    exact moment_norm n
  · exact moment_orthogonal n m h

/-- A concrete finite transform useful for the Gaussian/Laplace coefficient
calculation. This is a polynomial dilation identity, not an infinite generating
series or an assumed expansion of a physical source. -/
theorem moment_dilate (n : ℕ) (t : ℝ) :
    moment ((laguerre n).comp (C t * X)) =
      (momentWeight n / (n.factorial : ℝ)) * (1 - t) ^ n := by
  have hm (j : ℕ) (b : ℝ) :
      (monomial j b).comp (C t * X) = monomial j (b * t ^ j) := by
    rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow,
      ← mul_assoc, ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        momentWeight j * (coefficient n j * t ^ j) := by
      rw [laguerre, Polynomial.sum_comp, map_sum]
      simp_rw [hm, moment_monomial]
    _ = (momentWeight n / (n.factorial : ℝ)) *
        ∑ j ∈ Finset.range (n + 1),
          (-t) ^ j * (1 : ℝ) ^ (n - j) * (n.choose j : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [coefficient, neg_pow t j, one_pow, mul_one]
      field_simp [momentWeight_ne_zero j,
        show (n.factorial : ℝ) ≠ 0 by positivity]
      <;> ring
    _ = (momentWeight n / (n.factorial : ℝ)) * (1 - t) ^ n := by
      rw [← add_pow]
      congr 2
      ring

theorem moment_norm_pos (n : ℕ) : 0 < moment (laguerre n * laguerre n) := by
  rw [moment_norm]
  exact div_pos (momentWeight_pos n) (by positivity)

end FiniteGaussianCap4.LaguerreSevenHalf
