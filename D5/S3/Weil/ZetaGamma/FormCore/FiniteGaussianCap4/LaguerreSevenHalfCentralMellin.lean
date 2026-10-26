/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfCentralMellin
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual central Mellin modes and normalized finite Gaussian charge. -/
/-
SPDX-License-Identifier: Apache-2.0
UNCOMPILED source, 2026-10-26. No Lean/kernel or acceptance claim.

The actual central Mellin integral of the supplied alpha=7/2 polynomials.
The proof uses a NEW beta=9/4 finite moment map and the supplied polynomial
lowering and multiplication identities. It uses no series interchange.
The polynomial-induction integral realization follows the method of the
supplied LaguerreSevenHalfIntegral.lean (itself adapted from OAI commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0). The recurrence argument
and the change to beta=9/4 and dilation 2 are new here. Upstream notices and
licenses in the supplied modules remain applicable to those modules.
The applicable Apache-2.0 license is retained at LaguerreSevenHalfPolynomial.lean.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfGenerating
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Actual central Mellin modes and normalized finite Gaussian charge. -/

set_option autoImplicit false
noncomputable section

open Polynomial MeasureTheory Set
open scoped BigOperators

namespace FiniteGaussianCap4.LaguerreSevenHalf

/-- The actual beta=9/4 rising factorial, not an integral hypothesis. -/
def centralPochhammer (n : ℕ) : ℝ := (ascPochhammer ℝ n).eval (9 / 4)

@[simp] theorem centralPochhammer_zero : centralPochhammer 0 = 1 := by
  simp [centralPochhammer]

theorem centralPochhammer_succ (n : ℕ) :
    centralPochhammer (n + 1) = centralPochhammer n * ((9 / 4 : ℝ) + n) := by
  exact ascPochhammer_succ_eval n (9 / 4 : ℝ)

theorem centralPochhammer_pos (n : ℕ) : 0 < centralPochhammer n := by
  exact ascPochhammer_pos n (9 / 4 : ℝ) (by norm_num)

/-- The concrete finite moment of p(2x) against the normalized Gamma weight.
In particular this does not assume any Laguerre or Mellin coefficient. -/
def centralMoment : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun j => ((2 : ℝ) ^ j * centralPochhammer j) • LinearMap.id

@[simp] theorem centralMoment_monomial (j : ℕ) (a : ℝ) :
    centralMoment (monomial j a) = 2 ^ j * centralPochhammer j * a := by
  simp [centralMoment, Polynomial.lsum]

@[simp] theorem centralMoment_C (a : ℝ) : centralMoment (C a) = a := by
  simpa using centralMoment_monomial 0 a

@[simp] theorem centralMoment_one : centralMoment (1 : ℝ[X]) = 1 := by
  simpa using centralMoment_C 1

@[simp] theorem centralMoment_C_mul (a : ℝ) (p : ℝ[X]) :
    centralMoment (C a * p) = a * centralMoment p := by
  rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

/-- Finite Gamma integration by parts, proved on monomials and extended by
linearity. The factor 2 is essential: the polynomial argument is 2x. -/
theorem centralMoment_X_mul (p : ℝ[X]) :
    centralMoment (X * p) =
      2 * centralMoment (X * p.derivative) + (9 / 2 : ℝ) * centralMoment p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.derivative_add, mul_add, map_add]
      linear_combination hp + hq
  | monomial j a =>
      cases j with
      | zero =>
          simp only [Polynomial.monomial_zero_left, Polynomial.derivative_C,
            mul_zero, map_zero, zero_mul, zero_add, centralMoment_C]
          rw [Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial,
            centralMoment_monomial]
          norm_num [centralPochhammer_succ] <;> ring
      | succ j =>
          simp only [Polynomial.derivative_monomial_succ,
            Polynomial.X_mul_monomial, centralMoment_monomial,
            centralPochhammer_succ, pow_succ]
          push_cast
          ring

@[simp] theorem centralMoment_laguerre_zero : centralMoment (laguerre 0) = 1 := by
  simp

@[simp] theorem centralMoment_laguerre_one : centralMoment (laguerre 1) = 0 := by
  have hx := centralMoment_X_mul (1 : ℝ[X])
  have ht := congrArg (fun p : ℝ[X] => centralMoment p) X_laguerre_zero
  simp only [laguerre_zero, Polynomial.derivative_one, mul_zero, map_zero,
    mul_one, centralMoment_C, centralMoment_one, map_sub, centralMoment_C_mul] at hx ht
  linarith

/-- The actual parity-preserving recurrence. The middle mode cancels because
alpha+1=2 beta. It is derived from the actual supplied Laguerre polynomials. -/
theorem centralMoment_laguerre_step (n : ℕ) :
    ((n : ℝ) + 2) * centralMoment (laguerre (n + 2)) =
      ((n : ℝ) + 9 / 2) * centralMoment (laguerre n) := by
  have hx := centralMoment_X_mul (laguerre (n + 1))
  have hl := congrArg (fun p : ℝ[X] => centralMoment p) (lowering n)
  have ht := congrArg (fun p : ℝ[X] => centralMoment p) (X_laguerre_succ n)
  simp only [map_sub, centralMoment_C_mul] at hl
  simp only [add_mul, neg_mul, map_sub, map_add, map_neg,
    centralMoment_C_mul] at ht
  linear_combination ht - hx - 2 * hl

/-- Exact even scalar coefficient, proved and consumed by the integral below. -/
theorem centralMoment_laguerre_even (k : ℕ) :
    centralMoment (laguerre (2 * k)) =
      centralPochhammer k / (k.factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := centralMoment_laguerre_step (2 * k)
      rw [show 2 * k + 2 = 2 * (k + 1) by omega, ih] at h
      rw [centralPochhammer_succ, Nat.factorial_succ]
      push_cast at h ⊢
      have hf : (k.factorial : ℝ) ≠ 0 := by positivity
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      apply (eq_div_iff (mul_ne_zero hk hf)).2
      have h' := congrArg (fun r : ℝ => r * (k.factorial : ℝ)) h
      simp only [mul_assoc, div_mul_cancel₀ _ hf] at h'
      linear_combination h' / 2

/-- All actual odd scalar coefficients vanish; this is not a parity premise. -/
theorem centralMoment_laguerre_odd (k : ℕ) :
    centralMoment (laguerre (2 * k + 1)) = 0 := by
  induction k with
  | zero => simpa using centralMoment_laguerre_one
  | succ k ih =>
      have h := centralMoment_laguerre_step (2 * k + 1)
      rw [ih, mul_zero] at h
      have he : (2 * k + 1) + 2 = 2 * (k + 1) + 1 := by omega
      rw [he] at h
      exact (mul_eq_zero.mp h).resolve_left (by positivity)

theorem central_Gamma_shift (n : ℕ) :
    Real.Gamma ((n : ℝ) + 9 / 4) =
      Real.Gamma (9 / 4) * centralPochhammer n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have he : ((n + 1 : ℕ) : ℝ) + 9 / 4 = ((n : ℝ) + 9 / 4) + 1 := by
        push_cast
        ring
      rw [he, Real.Gamma_add_one (by positivity), ih, centralPochhammer_succ]
      ring

private theorem central_monomial_eq (n : ℕ) (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) * x ^ (5 / 4 : ℝ) * x ^ n =
      Real.exp (-x) * x ^ (((n : ℝ) + 9 / 4) - 1) := by
  rw [show ((n : ℝ) + 9 / 4) - 1 = (5 / 4 : ℝ) + n by ring,
    Real.rpow_add hx, Real.rpow_natCast]
  ring

theorem integrable_central_monomial (n : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (5 / 4 : ℝ) * x ^ n)
      (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (n : ℝ) + 9 / 4) (by positivity)
  exact h.congr_fun (fun x hx => (central_monomial_eq n x hx).symm) measurableSet_Ioi

theorem integral_central_monomial (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (5 / 4 : ℝ) * x ^ n) =
      Real.Gamma (9 / 4) * centralPochhammer n := by
  calc
    _ = ∫ x in Ioi (0 : ℝ),
        Real.exp (-x) * x ^ (((n : ℝ) + 9 / 4) - 1) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => central_monomial_eq n x hx)
    _ = Real.Gamma ((n : ℝ) + 9 / 4) :=
      (Real.Gamma_eq_integral (by positivity)).symm
    _ = _ := central_Gamma_shift n

/-- Genuine L1 domain of the finite polynomial integral, including dilation. -/
theorem integrable_central_polynomial (p : ℝ[X]) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (-x) * x ^ (5 / 4 : ℝ) * p.eval (2 * x)) (Ioi 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert hp.add hq using 1
      funext x
      simp only [Polynomial.eval_add, mul_add, Pi.add_apply]
  | monomial n a =>
      change Integrable _ (volume.restrict (Ioi 0))
      convert (integrable_central_monomial n).const_mul (a * 2 ^ n) using 1
      funext x
      simp only [Polynomial.eval_monomial, mul_pow]
      ring

/-- Integral realization of the new finite moment map, not an assumed
central-mode coefficient. Only finite polynomial induction is used. -/
theorem integral_central_polynomial (p : ℝ[X]) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-x) * x ^ (5 / 4 : ℝ) * p.eval (2 * x)) =
      Real.Gamma (9 / 4) * centralMoment p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.eval_add, mul_add]
      rw [integral_add (integrable_central_polynomial p)
        (integrable_central_polynomial q), hp, hq, map_add]
      ring
  | monomial n a =>
      simp only [Polynomial.eval_monomial, centralMoment_monomial]
      calc
        _ = ∫ x in Ioi (0 : ℝ),
            (a * 2 ^ n) * (Real.exp (-x) * x ^ (5 / 4 : ℝ) * x ^ n) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          dsimp only
          rw [mul_pow]
          ring
        _ = (a * 2 ^ n) * (Real.Gamma (9 / 4) * centralPochhammer n) := by
          rw [integral_const_mul, integral_central_monomial]
        _ = _ := by ring

/-- J_n is the literal integral of the supplied phi, at beta=9/4. -/
def centralMellinIntegral (n : ℕ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x ^ (5 / 4 : ℝ) * phi x n

theorem integrable_central_phi (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (5 / 4 : ℝ) * phi x n) (Ioi 0) := by
  convert integrable_central_polynomial (laguerre n) using 1
  funext x
  simp only [phi]
  ring

theorem centralMellinIntegral_eq_moment (n : ℕ) :
    centralMellinIntegral n = Real.Gamma (9 / 4) * centralMoment (laguerre n) := by
  calc
    _ = ∫ x in Ioi (0 : ℝ),
        Real.exp (-x) * x ^ (5 / 4 : ℝ) * (laguerre n).eval (2 * x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [phi]
      ring
    _ = _ := integral_central_polynomial (laguerre n)

@[simp] theorem centralMellinIntegral_zero :
    centralMellinIntegral 0 = Real.Gamma (9 / 4) := by
  simp [centralMellinIntegral_eq_moment]

@[simp] theorem centralMellinIntegral_one : centralMellinIntegral 1 = 0 := by
  simp [centralMellinIntegral_eq_moment]

theorem centralMellinIntegral_step (n : ℕ) :
    ((n : ℝ) + 2) * centralMellinIntegral (n + 2) =
      ((n : ℝ) + 9 / 2) * centralMellinIntegral n := by
  rw [centralMellinIntegral_eq_moment, centralMellinIntegral_eq_moment]
  linear_combination Real.Gamma (9 / 4) * centralMoment_laguerre_step n

theorem centralMellinIntegral_even (k : ℕ) :
    centralMellinIntegral (2 * k) =
      Real.Gamma (9 / 4) * centralPochhammer k / (k.factorial : ℝ) := by
  rw [centralMellinIntegral_eq_moment, centralMoment_laguerre_even]
  ring

theorem centralMellinIntegral_odd (k : ℕ) :
    centralMellinIntegral (2 * k + 1) = 0 := by
  rw [centralMellinIntegral_eq_moment, centralMoment_laguerre_odd, mul_zero]

theorem centralMellinIntegral_even_pos (k : ℕ) :
    0 < centralMellinIntegral (2 * k) := by
  rw [centralMellinIntegral_even]
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos (by norm_num))
    (centralPochhammer_pos k)) (by positivity)

end FiniteGaussianCap4.LaguerreSevenHalf
