/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfJacobi
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual finite Gaussian graph convergence and normalized Jacobi transport. -/
/-
SPDX-License-Identifier: Apache-2.0
UNCOMPILED source, 2026-10-26. No kernel or acceptance claim.

New normalization, multiplication and finite polynomial-pair proofs, using
the supplied actual alpha=7/2 polynomials, moments and centralNormalization.
The imported polynomial/moment/integral sources retain their OAI attribution
(commit adc7f1241b42e322a6451854ab7e4b4c146bf78a) and Apache-2.0 license.
No external proof body is copied here. No completeness premise is used.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfCentralNormalization
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Polynomial MeasureTheory Set
open scoped BigOperators

namespace FiniteGaussianCap4.LaguerreSevenHalf

def jacobiUpper (n : ℕ) : ℝ :=
  Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 9 / 2)) / 2

theorem jacobiUpper_nonneg (n : ℕ) : 0 ≤ jacobiUpper n := by
  exact div_nonneg (Real.sqrt_nonneg _) (by norm_num)

theorem jacobiUpper_sq (n : ℕ) :
    jacobiUpper n ^ 2 = (((n : ℝ) + 1) * ((n : ℝ) + 9 / 2)) / 4 := by
  rw [jacobiUpper, div_pow, Real.sq_sqrt (by positivity)]
  norm_num

theorem normalization_upper (n : ℕ) :
    jacobiUpper n * centralNormalization (n + 1) =
      (((n : ℝ) + 1) / 2) * centralNormalization n := by
  apply (sq_eq_sq₀ (mul_nonneg (jacobiUpper_nonneg n)
    (centralNormalization_pos _).le)
    (mul_nonneg (by positivity) (centralNormalization_pos _).le)).1
  rw [mul_pow, jacobiUpper_sq, centralNormalization_sq_step]
  field_simp [show (n : ℝ) + 9 / 2 ≠ 0 by positivity]
  <;> ring

theorem normalization_lower (n : ℕ) :
    jacobiUpper n * centralNormalization n =
      (((n : ℝ) + 9 / 2) / 2) * centralNormalization (n + 1) := by
  apply (sq_eq_sq₀ (mul_nonneg (jacobiUpper_nonneg n)
    (centralNormalization_pos _).le)
    (mul_nonneg (by positivity) (centralNormalization_pos _).le)).1
  rw [mul_pow, jacobiUpper_sq, mul_pow, centralNormalization_sq_step]
  field_simp [show (n : ℝ) + 9 / 2 ≠ 0 by positivity]
  <;> ring

/-- The actual normalized polynomial; this uses, rather than replaces, N_n. -/
def psiPolynomial (n : ℕ) : ℝ[X] := C (centralNormalization n) * laguerre n

def physicalPolynomial (p : ℝ[X]) (x : ℝ) : ℝ :=
  Real.exp (-x) * p.eval (2 * x)

@[simp] theorem physicalPolynomial_psi (n : ℕ) (x : ℝ) :
    physicalPolynomial (psiPolynomial n) x = centralPsi x n := by
  simp only [physicalPolynomial, psiPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, centralPsi, phi]
  ring

@[simp] theorem physicalPolynomial_sub (p q : ℝ[X]) (x : ℝ) :
    physicalPolynomial (p - q) x = physicalPolynomial p x - physicalPolynomial q x := by
  simp only [physicalPolynomial, Polynomial.eval_sub, mul_sub]

@[simp] theorem physicalPolynomial_C (a : ℝ) (p : ℝ[X]) (x : ℝ) :
    physicalPolynomial (C a * p) x = a * physicalPolynomial p x := by
  simp only [physicalPolynomial, Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- Multiplication by the physical variable, whose polynomial argument is 2x. -/
def physicalX (p : ℝ[X]) : ℝ[X] := C (1 / 2 : ℝ) * X * p

@[simp] theorem physicalPolynomial_X (p : ℝ[X]) (x : ℝ) :
    physicalPolynomial (physicalX p) x = x * physicalPolynomial p x := by
  simp only [physicalPolynomial, physicalX, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem physicalX_psi_zero :
    physicalX (psiPolynomial 0) =
      C (9 / 4 : ℝ) * psiPolynomial 0 - C (jacobiUpper 0) * psiPolynomial 1 := by
  have hN : jacobiUpper 0 * centralNormalization 1 = centralNormalization 0 / 2 := by
    simpa only [Nat.cast_zero, zero_add, one_div, div_eq_mul_inv, mul_comm, one_mul] using normalization_upper 0
  have hM : (centralNormalization 0 / 2) * (9 / 2 : ℝ) = (9 / 4 : ℝ) * centralNormalization 0 := by
    ring
  calc
    _ = C (centralNormalization 0 / 2) * (X * laguerre 0) := by
      simp only [physicalX, psiPolynomial, div_eq_mul_inv, map_mul, map_one]
      ring
    _ = C (centralNormalization 0 / 2) *
        (C (9 / 2 : ℝ) * laguerre 0 - laguerre 1) := by rw [X_laguerre_zero]
    _ = _ := by
      simp only [psiPolynomial, mul_sub, ← mul_assoc, ← Polynomial.C_mul]
      rw [hM, hN]

theorem physicalX_psi_succ (n : ℕ) :
    physicalX (psiPolynomial (n + 1)) =
      C ((n : ℝ) + 1 + 9 / 4) * psiPolynomial (n + 1) -
        C (jacobiUpper (n + 1)) * psiPolynomial (n + 2) -
        C (jacobiUpper n) * psiPolynomial n := by
  have hu : (centralNormalization (n + 1) / 2) * ((n : ℝ) + 2) =
      jacobiUpper (n + 1) * centralNormalization (n + 2) := by
    have h := normalization_upper (n + 1)
    push_cast at h
    rw [h]
    ring
  have hl : (centralNormalization (n + 1) / 2) * ((n : ℝ) + 9 / 2) =
      jacobiUpper n * centralNormalization n := by
    rw [normalization_lower]
    ring
  have hm : (centralNormalization (n + 1) / 2) * (2 * (n : ℝ) + 9 / 2 + 2) =
      ((n : ℝ) + 1 + 9 / 4) * centralNormalization (n + 1) := by ring
  calc
    _ = C (centralNormalization (n + 1) / 2) * (X * laguerre (n + 1)) := by
      simp only [physicalX, psiPolynomial, div_eq_mul_inv, map_mul, map_one]
      ring
    _ = C (centralNormalization (n + 1) / 2) *
        (-C ((n : ℝ) + 2) * laguerre (n + 2) +
          C (2 * (n : ℝ) + 9 / 2 + 2) * laguerre (n + 1) -
          C ((n : ℝ) + 9 / 2) * laguerre n) := by rw [X_laguerre_succ]
    _ = _ := by
      simp only [psiPolynomial, mul_add, mul_sub, mul_neg, ← mul_assoc, ← Polynomial.C_mul]
      simp only [mul_add, ← mul_assoc] at hu hl hm
      rw [hu, hl, hm]
      ring

/-- Literal n=0 endpoint. No predecessor at a natural negative index. -/
theorem centralPsi_mul_x_zero (x : ℝ) :
    x * centralPsi x 0 = (9 / 4 : ℝ) * centralPsi x 0 -
      jacobiUpper 0 * centralPsi x 1 := by
  have h := congrArg (fun p : ℝ[X] => physicalPolynomial p x) physicalX_psi_zero
  simpa only [physicalPolynomial_X, physicalPolynomial_sub, physicalPolynomial_C,
    physicalPolynomial_psi] using h

/-- Literal successor recurrence with beta=9/4. -/
theorem centralPsi_mul_x_succ (n : ℕ) (x : ℝ) :
    x * centralPsi x (n + 1) = ((n : ℝ) + 1 + 9 / 4) * centralPsi x (n + 1) -
      jacobiUpper (n + 1) * centralPsi x (n + 2) -
      jacobiUpper n * centralPsi x n := by
  have h := congrArg (fun p : ℝ[X] => physicalPolynomial p x) (physicalX_psi_succ n)
  simpa only [physicalPolynomial_X, physicalPolynomial_sub, physicalPolynomial_C,
    physicalPolynomial_psi] using h

/-- One statement in exactly the requested indexing convention, with n=0 safe. -/
theorem centralPsi_mul_x (n : ℕ) (x : ℝ) :
    x * centralPsi x n = ((n : ℝ) + 9 / 4) * centralPsi x n -
      (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 9 / 2)) / 2) * centralPsi x (n + 1) -
      (Real.sqrt ((n : ℝ) * ((n : ℝ) + 7 / 2)) / 2) * centralPsi x (n - 1) := by
  cases n with
  | zero => simpa [jacobiUpper] using centralPsi_mul_x_zero x
  | succ n =>
      have he : ((n : ℝ) + 1) * ((n : ℝ) + 1 + 7 / 2) =
          ((n : ℝ) + 1) * ((n : ℝ) + 9 / 2) := by ring
      simpa only [jacobiUpper, Nat.cast_add, Nat.cast_succ, Nat.cast_one, Nat.add_sub_cancel, he] using
        centralPsi_mul_x_succ n x

/-- A concrete finite polynomial pairing, subsequently realized as an integral. -/
def polynomialPair (p q : ℝ[X]) : ℝ :=
  Real.Gamma (9 / 2) * moment (p * q) / (2 : ℝ) ^ (9 / 2 : ℝ)

@[simp] theorem polynomialPair_zero_left (q : ℝ[X]) : polynomialPair 0 q = 0 := by
  simp [polynomialPair]

theorem polynomialPair_comm (p q : ℝ[X]) : polynomialPair p q = polynomialPair q p := by
  simp only [polynomialPair, mul_comm p q]

@[simp] theorem polynomialPair_add_left (p q r : ℝ[X]) :
    polynomialPair (p + q) r = polynomialPair p r + polynomialPair q r := by
  simp only [polynomialPair, add_mul, map_add]
  ring

@[simp] theorem polynomialPair_sub_left (p q r : ℝ[X]) :
    polynomialPair (p - q) r = polynomialPair p r - polynomialPair q r := by
  simp only [polynomialPair, sub_mul, map_sub]
  ring

@[simp] theorem polynomialPair_C_left (a : ℝ) (p q : ℝ[X]) :
    polynomialPair (C a * p) q = a * polynomialPair p q := by
  simp only [polynomialPair, mul_assoc, moment_C_mul]
  ring

@[simp] theorem polynomialPair_add_right (p q r : ℝ[X]) :
    polynomialPair p (q + r) = polynomialPair p q + polynomialPair p r := by
  simpa only [polynomialPair_comm] using polynomialPair_add_left q r p

@[simp] theorem polynomialPair_sub_right (p q r : ℝ[X]) :
    polynomialPair p (q - r) = polynomialPair p q - polynomialPair p r := by
  simpa only [polynomialPair_comm] using polynomialPair_sub_left q r p

@[simp] theorem polynomialPair_C_right (a : ℝ) (p q : ℝ[X]) :
    polynomialPair p (C a * q) = a * polynomialPair p q := by
  simpa only [polynomialPair_comm] using polynomialPair_C_left a q p

theorem polynomialPair_sum_left {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) (q : ℝ[X]) :
    polynomialPair (∑ i ∈ s, p i) q = ∑ i ∈ s, polynomialPair (p i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem weighted_scaled_polynomial (p : ℝ[X]) (x : ℝ) (hx : 0 < x) :
    x ^ (7 / 2 : ℝ) * Real.exp (-x) * Real.exp (-x) * p.eval (2 * x) =
      (1 / (2 : ℝ) ^ (7 / 2 : ℝ)) *
        (Real.exp (-(2 * x)) * (2 * x) ^ (7 / 2 : ℝ) * p.eval (2 * x)) := by
  rw [Real.mul_rpow (by norm_num) hx.le]
  have he : Real.exp (-x) * Real.exp (-x) = Real.exp (-(2 * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show x ^ (7 / 2 : ℝ) * Real.exp (-x) * Real.exp (-x) =
      x ^ (7 / 2 : ℝ) * (Real.exp (-x) * Real.exp (-x)) by ring, he]
  field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (7 / 2)).ne']
  <;> ring

theorem integrable_physical_product (p q : ℝ[X]) :
    IntegrableOn (fun x => x ^ (7 / 2 : ℝ) *
      physicalPolynomial p x * physicalPolynomial q x) (Ioi 0) := by
  have hg := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => Real.exp (-x) * x ^ (7 / 2 : ℝ) * (p * q).eval x)
    0 (by norm_num : (0 : ℝ) < 2)).2
      (by simpa using integrable_weighted_polynomial (p * q))
  have hscaled : IntegrableOn (fun x : ℝ => (1 / (2 : ℝ) ^ (7 / 2 : ℝ)) *
      (Real.exp (-(2 * x)) * (2 * x) ^ (7 / 2 : ℝ) * (p * q).eval (2 * x))) (Ioi 0) :=
    hg.const_mul (1 / (2 : ℝ) ^ (7 / 2 : ℝ))
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro x hx
  dsimp only
  rw [← weighted_scaled_polynomial (p * q) x hx]
  simp only [physicalPolynomial, Polynomial.eval_mul]
  ring

theorem integral_physical_product (p q : ℝ[X]) :
    (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
      physicalPolynomial p x * physicalPolynomial q x) = polynomialPair p q := by
  have he : (2 : ℝ) ^ (9 / 2 : ℝ) =
      (2 : ℝ) ^ (7 / 2 : ℝ) * 2 := by
    rw [show (9 / 2 : ℝ) = 7 / 2 + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  calc
    _ = ∫ x in Ioi (0 : ℝ), (1 / (2 : ℝ) ^ (7 / 2 : ℝ)) *
        (Real.exp (-(2 * x)) * (2 * x) ^ (7 / 2 : ℝ) * (p * q).eval (2 * x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [← weighted_scaled_polynomial (p * q) x hx]
      simp only [physicalPolynomial, Polynomial.eval_mul]
      ring
    _ = (1 / (2 : ℝ) ^ (7 / 2 : ℝ)) *
        ((2 : ℝ)⁻¹ * (Real.Gamma (9 / 2) * moment (p * q))) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi
        (fun y : ℝ => Real.exp (-y) * y ^ (7 / 2 : ℝ) * (p * q).eval y)
        0 (by norm_num : (0 : ℝ) < 2)]
      simp only [mul_zero, smul_eq_mul, integral_weighted_polynomial]
    _ = _ := by
      rw [polynomialPair, he]
      field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (7 / 2)).ne']
      <;> ring

/-- Actual normalized orthogonality, derived from the supplied moments. -/
@[simp] theorem polynomialPair_psi (n m : ℕ) :
    polynomialPair (psiPolynomial n) (psiPolynomial m) = if n = m then 1 else 0 := by
  rw [psiPolynomial, psiPolynomial, polynomialPair_C_left, polynomialPair_C_right]
  unfold polynomialPair
  rw [moment_product]
  split_ifs with h
  · subst m
    have hG := Gamma_eq_momentWeight n
    have hN := centralNormalization_sq n
    have h2 := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (9 / 2)
    have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
    have hG0 : Real.Gamma (9 / 2) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 9 / 2)).ne'
    rw [hG] at hN
    have hmw := momentWeight_ne_zero n
    field_simp [hfac, h2.ne', hmw, hG0] at hN ⊢
    nlinarith [hN]
  · simp

theorem centralPsi_integral_product (n m : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * centralPsi x n * centralPsi x m) =
      if n = m then 1 else 0 := by
  simpa only [physicalPolynomial_psi] using
    (integral_physical_product (psiPolynomial n) (psiPolynomial m)).trans (polynomialPair_psi n m)

/-- Actual central charge in the rational recurrence coordinates used by the
finite matrix calculation. The sequence is supplied by the consumer. -/
theorem centralCharge_normalization_transport (a : ℕ → ℝ)
    (ha0 : a 0 = 1)
    (hstep : ∀ k : ℕ, a (k + 1) = a k * ((k : ℝ) + 1 / 2) / ((k : ℝ) + 11 / 4))
    (k : ℕ) :
    (normalizedCentralMellin (2 * k) / normalizedCentralMellin 0) *
      centralNormalization (2 * k) = centralNormalization 0 * a k := by
  have htstep (j : ℕ) :
      centralNormalization (2 * (j + 1)) ^ 2 * centralMellinIntegral (2 * (j + 1)) =
        ((j : ℝ) + 1 / 2) / ((j : ℝ) + 11 / 4) *
          (centralNormalization (2 * j) ^ 2 * centralMellinIntegral (2 * j)) := by
    have hJ : centralMellinIntegral (2 * j + 2) =
        ((((2 * j : ℕ) : ℝ) + 9 / 2) / (((2 * j : ℕ) : ℝ) + 2)) *
          centralMellinIntegral (2 * j) := by
      rw [div_mul_eq_mul_div₀]
      apply (eq_div_iff (show (((2 * j : ℕ) : ℝ) + 2) ≠ 0 by positivity)).2
      linear_combination centralMellinIntegral_step (2 * j)
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, hJ,
      show 2 * j + 2 = (2 * j + 1) + 1 by omega,
      centralNormalization_sq_step, centralNormalization_sq_step]
    push_cast
    field_simp [show 2 * (j : ℝ) + 9 / 2 ≠ 0 by positivity,
      show 2 * (j : ℝ) + 1 + 9 / 2 ≠ 0 by positivity,
      show 2 * (j : ℝ) + 2 ≠ 0 by positivity,
      show (j : ℝ) + 11 / 4 ≠ 0 by positivity]
    <;> ring
  have ht (j : ℕ) :
      centralNormalization (2 * j) ^ 2 * centralMellinIntegral (2 * j) =
        centralNormalization 0 ^ 2 * centralMellinIntegral 0 * a j := by
    induction j with
    | zero => simp only [Nat.mul_zero, ha0, mul_one]
    | succ j ih =>
        rw [htstep, ih, hstep]
        ring
  calc
    _ = (centralNormalization (2 * k) ^ 2 * centralMellinIntegral (2 * k)) /
        (centralNormalization 0 * centralMellinIntegral 0) := by
      rw [normalizedCentralMellin_eq, normalizedCentralMellin_eq]
      ring
    _ = (centralNormalization 0 ^ 2 * centralMellinIntegral 0 * a k) /
        (centralNormalization 0 * centralMellinIntegral 0) := by rw [ht]
    _ = _ := by
      have hJ0 : centralMellinIntegral 0 ≠ 0 := (centralMellinIntegral_even_pos 0).ne'
      field_simp [(centralNormalization_pos 0).ne', hJ0]
      <;> ring

/-- The exact base normalization needed by the finite matrix certificate. -/
theorem centralNormalization_zero_sq_exact :
    centralNormalization 0 ^ 2 = 256 * Real.sqrt 2 / (105 * Real.sqrt Real.pi) := by
  have hG : Real.Gamma (9 / 2) = (105 / 16 : ℝ) * Real.sqrt Real.pi := by
    have h := Real.Gamma_nat_add_half 4
    norm_num [Nat.doubleFactorial] at h
    linarith
  have hpow : (2 : ℝ) ^ (9 / 2 : ℝ) = 16 * Real.sqrt 2 := by
    rw [show (9 / 2 : ℝ) = 4 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num), ← Real.sqrt_eq_rpow]
    norm_num
  rw [centralNormalization_sq]
  simp only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one, mul_one]
  rw [hG, hpow]
  field_simp [(Real.sqrt_pos.2 Real.pi_pos).ne']
  <;> ring

end FiniteGaussianCap4.LaguerreSevenHalf
