/-
UNCOMPILED source proposal, 2026-10-26. No kernel or official acceptance claim.
SPDX-License-Identifier: Apache-2.0

Modified/adapted proof method from the OAI project, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a,
lean/OAI/MathematicalPhysics/DefocusingNLS/Certificates/LaguerrePolynomial.lean.
That source treats alpha=0 over C. This file changes the coefficients, scalar
field, ODE, and recurrences to alpha=7/2; it does not import OAI or reuse an
alpha=0 conclusion at a different parameter. See ../LICENSE-OAI for the
applicable upstream Apache-2.0 license.
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped BigOperators

namespace FiniteGaussianCap4.LaguerreSevenHalf

/-- `(9/2)_n`; Gamma(9/2) has been divided out of the moments. -/
def momentWeight (n : ℕ) : ℝ := (ascPochhammer ℝ n).eval (9 / 2)

@[simp] theorem momentWeight_zero : momentWeight 0 = 1 := by
  simp [momentWeight]

theorem momentWeight_succ (n : ℕ) :
    momentWeight (n + 1) = momentWeight n * ((9 / 2 : ℝ) + n) := by
  exact ascPochhammer_succ_eval n (9 / 2 : ℝ)

theorem momentWeight_pos (n : ℕ) : 0 < momentWeight n := by
  exact ascPochhammer_pos n (9 / 2 : ℝ) (by norm_num)

theorem momentWeight_ne_zero (n : ℕ) : momentWeight n ≠ 0 :=
  (momentWeight_pos n).ne'

private theorem factorial_real_ne_zero (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by
  positivity

/-- Exact generalized Laguerre convention:
`[X^j] L_n^(7/2) = (-1)^j choose(n,j) (9/2)_n / ((9/2)_j n!)`.
The coefficient is zero beyond n. The theorem `coefficient_add` gives the
usual trailing-Pochhammer divided by `j! (n-j)!` form. -/
def coefficient (n j : ℕ) : ℝ :=
  (-1) ^ j * (n.choose j : ℝ) * momentWeight n /
    (momentWeight j * (n.factorial : ℝ))

def laguerre (n : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1), monomial j (coefficient n j)

theorem coefficient_eq_zero (n j : ℕ) (h : n < j) : coefficient n j = 0 := by
  simp [coefficient, Nat.choose_eq_zero_of_lt h]

@[simp] theorem coeff_laguerre (n j : ℕ) :
    (laguerre n).coeff j = coefficient n j := by
  by_cases h : j < n + 1
  · simp [laguerre, Polynomial.coeff_monomial, Finset.mem_range, h]
  · have hnj : n < j := by omega
    simp [laguerre, Polynomial.coeff_monomial, Finset.mem_range, h,
      coefficient_eq_zero n j hnj]

@[simp] theorem coefficient_zero (n : ℕ) :
    coefficient n 0 = momentWeight n / (n.factorial : ℝ) := by
  simp [coefficient]

@[simp] theorem coefficient_self (n : ℕ) :
    coefficient n n = (-1 : ℝ) ^ n / (n.factorial : ℝ) := by
  simp only [coefficient, Nat.choose_self, Nat.cast_one, mul_one]
  field_simp [momentWeight_ne_zero n, factorial_real_ne_zero n]
  <;> ring

@[simp] theorem laguerre_eval_zero (n : ℕ) :
    (laguerre n).eval 0 = momentWeight n / (n.factorial : ℝ) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_laguerre, coefficient_zero]

@[simp] theorem laguerre_zero : laguerre 0 = 1 := by
  ext j
  cases j with
  | zero => simp
  | succ j =>
      simp [Polynomial.coeff_one, coefficient_eq_zero 0 (j + 1) (by omega)]

/-- Explicit finite polynomial expansion, with no basis assumption. -/
theorem laguerre_eval (n : ℕ) (x : ℝ) :
    (laguerre n).eval x =
      ∑ j ∈ Finset.range (n + 1), coefficient n j * x ^ j := by
  simp [laguerre, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Compatibility with the standard coefficient
`(-1)^j (9/2+j)_r / (j! r!)` at degree n=j+r. -/
theorem coefficient_add (j r : ℕ) :
    coefficient (j + r) j =
      (-1 : ℝ) ^ j * (ascPochhammer ℝ r).eval ((9 / 2 : ℝ) + j) /
        ((j.factorial : ℝ) * (r.factorial : ℝ)) := by
  have hw : momentWeight (j + r) =
      momentWeight j * (ascPochhammer ℝ r).eval ((9 / 2 : ℝ) + j) := by
    have h := congrArg (fun p : ℝ[X] => p.eval (9 / 2))
      (ascPochhammer_mul ℝ j r)
    simpa [momentWeight, Polynomial.eval_comp] using h.symm
  have hc : ((j + r).choose j : ℝ) * (j.factorial : ℝ) *
      (r.factorial : ℝ) = ((j + r).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j r)
    simpa only [Nat.add_sub_cancel_left, Nat.cast_mul] using
      congrArg (fun a : ℕ => (a : ℝ)) h
  have hc' : ((j + r).choose j : ℝ) =
      ((j + r).factorial : ℝ) / ((j.factorial : ℝ) * (r.factorial : ℝ)) := by
    apply (eq_div_iff (mul_ne_zero (factorial_real_ne_zero j)
      (factorial_real_ne_zero r))).2
    simpa only [mul_assoc] using hc
  rw [coefficient, hw, hc']
  field_simp [momentWeight_ne_zero j, factorial_real_ne_zero j,
    factorial_real_ne_zero r, factorial_real_ne_zero (j + r)]
  <;> ring

/-- The recurrence which is exactly the coefficient form of the alpha=7/2 ODE. -/
theorem coefficient_recurrence (n j : ℕ) :
    ((j : ℝ) + 1) * ((j : ℝ) + 9 / 2) * coefficient n (j + 1) +
      ((n : ℝ) - j) * coefficient n j = 0 := by
  by_cases hjn : j ≤ n
  · have hc : (n.choose (j + 1) : ℝ) * ((j : ℝ) + 1) =
        (n.choose j : ℝ) * ((n : ℝ) - j) := by
      have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq n j)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hjn] using h
    have hj : (9 / 2 : ℝ) + j ≠ 0 := by positivity
    calc
      _ = ((-1 : ℝ) ^ j * momentWeight n /
          (momentWeight j * (n.factorial : ℝ))) *
          (-(n.choose (j + 1) : ℝ) * ((j : ℝ) + 1) +
            (n.choose j : ℝ) * ((n : ℝ) - j)) := by
        simp only [coefficient, momentWeight_succ, pow_succ]
        field_simp [momentWeight_ne_zero j, factorial_real_ne_zero n, hj]
        <;> ring
      _ = 0 := by rw [neg_mul, hc]; ring
  · have hnj : n < j := by omega
    rw [coefficient_eq_zero n j hnj,
      coefficient_eq_zero n (j + 1) (by omega)]
    ring

/-- `X L'' +(9/2-X)L' + n L = 0`, as an actual polynomial identity. -/
theorem differential_equation (n : ℕ) :
    X * (laguerre n).derivative.derivative +
      (C (9 / 2 : ℝ) - X) * (laguerre n).derivative +
      C (n : ℝ) * laguerre n = 0 := by
  ext j
  cases j with
  | zero =>
      simpa [Polynomial.coeff_add, Polynomial.coeff_sub,
        Polynomial.coeff_derivative, sub_mul, Polynomial.coeff_C_mul] using
        coefficient_recurrence n 0
  | succ j =>
      simp only [Polynomial.coeff_add, sub_mul, Polynomial.coeff_sub,
        Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
        Polynomial.coeff_C_mul, coeff_laguerre, Polynomial.coeff_zero]
      have h := coefficient_recurrence n (j + 1)
      push_cast at h ⊢
      linear_combination h

/-- A finite coefficient identity, valid even when j exceeds n. -/
theorem coefficient_derivative_step (n j : ℕ) :
    ((j : ℝ) + 1) * (coefficient (n + 1) (j + 1) -
      coefficient n (j + 1)) = -coefficient n j := by
  have hpas : ((n + 1).choose (j + 1) : ℝ) =
      (n.choose j : ℝ) + (n.choose (j + 1) : ℝ) := by
    exact_mod_cast Nat.choose_succ_succ' n j
  have hmul : ((n : ℝ) + 1) * (n.choose j : ℝ) =
      ((n + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n j
  rw [hpas] at hmul
  have hc : -((j : ℝ) + 1) * ((n : ℝ) + 9 / 2) *
        ((n + 1).choose (j + 1) : ℝ) +
      ((j : ℝ) + 1) * ((n : ℝ) + 1) * (n.choose (j + 1) : ℝ) +
      ((9 / 2 : ℝ) + j) * ((n : ℝ) + 1) * (n.choose j : ℝ) = 0 := by
    rw [hpas]
    linear_combination ((9 / 2 : ℝ) - 1) * hmul
  have hj : (9 / 2 : ℝ) + j ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hz : ((j : ℝ) + 1) * (coefficient (n + 1) (j + 1) -
      coefficient n (j + 1)) + coefficient n j = 0 := by
    calc
      _ = ((-1 : ℝ) ^ j * momentWeight n /
          (momentWeight j * (n.factorial : ℝ) *
            ((n : ℝ) + 1) * ((9 / 2 : ℝ) + j))) *
          (-((j : ℝ) + 1) * ((n : ℝ) + 9 / 2) *
              ((n + 1).choose (j + 1) : ℝ) +
            ((j : ℝ) + 1) * ((n : ℝ) + 1) * (n.choose (j + 1) : ℝ) +
            ((9 / 2 : ℝ) + j) * ((n : ℝ) + 1) * (n.choose j : ℝ)) := by
        simp only [coefficient, momentWeight_succ, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        field_simp [momentWeight_ne_zero j, factorial_real_ne_zero n, hj, hn]
        <;> ring
      _ = 0 := by rw [hc, mul_zero]
  linear_combination hz

/-- The parameter-preserving first derivative step. -/
theorem derivative_step (n : ℕ) :
    (laguerre (n + 1)).derivative = (laguerre n).derivative - laguerre n := by
  ext j
  simp only [Polynomial.coeff_sub, Polynomial.coeff_derivative, coeff_laguerre]
  have h := coefficient_derivative_step n j
  linear_combination h

/-- Lowering identity in coefficient form. -/
theorem coefficient_lowering (n j : ℕ) :
    (j : ℝ) * coefficient (n + 1) j =
      ((n : ℝ) + 1) * coefficient (n + 1) j -
        ((n : ℝ) + 9 / 2) * coefficient n j := by
  by_cases hj : j ≤ n + 1
  · have hc0 : (n.choose j : ℝ) * ((n : ℝ) + 1) =
        ((n + 1).choose j : ℝ) * (((n : ℝ) + 1) - j) := by
      have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_mul_succ_eq n j)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj] using h
    have hc : ((j : ℝ) - ((n : ℝ) + 1)) * ((n + 1).choose j : ℝ) +
        ((n : ℝ) + 1) * (n.choose j : ℝ) = 0 := by
      linear_combination hc0
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hz : (j : ℝ) * coefficient (n + 1) j -
        (((n : ℝ) + 1) * coefficient (n + 1) j -
          ((n : ℝ) + 9 / 2) * coefficient n j) = 0 := by
      calc
        _ = ((-1 : ℝ) ^ j * momentWeight n * ((n : ℝ) + 9 / 2) /
            (momentWeight j * (n.factorial : ℝ) * ((n : ℝ) + 1))) *
            (((j : ℝ) - ((n : ℝ) + 1)) * ((n + 1).choose j : ℝ) +
              ((n : ℝ) + 1) * (n.choose j : ℝ)) := by
          simp only [coefficient, momentWeight_succ, Nat.factorial_succ,
            Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp [momentWeight_ne_zero j, factorial_real_ne_zero n, hn]
          <;> ring
        _ = 0 := by rw [hc, mul_zero]
    linear_combination hz
  · rw [coefficient_eq_zero (n + 1) j (by omega),
      coefficient_eq_zero n j (by omega)]
    ring

/-- `X L_(n+1)' = (n+1)L_(n+1) -(n+9/2)L_n`. -/
theorem lowering (n : ℕ) :
    X * (laguerre (n + 1)).derivative =
      C ((n : ℝ) + 1) * laguerre (n + 1) -
        C ((n : ℝ) + 9 / 2) * laguerre n := by
  ext j
  cases j with
  | zero =>
      simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul_zero, coeff_laguerre, Nat.cast_zero, zero_mul]
        using coefficient_lowering n 0
  | succ j =>
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_mul, Polynomial.coeff_derivative, coeff_laguerre]
      have h := coefficient_lowering n (j + 1)
      push_cast at h ⊢
      linear_combination h

/-- Degree-zero endpoint of the multiplication-by-X recurrence. -/
theorem X_laguerre_zero :
    X * laguerre 0 = C (9 / 2 : ℝ) * laguerre 0 - laguerre 1 := by
  have h := lowering 0
  rw [derivative_step] at h
  simp only [laguerre_zero, Polynomial.derivative_one, zero_sub, mul_neg,
    mul_one, Nat.cast_zero, zero_add, Polynomial.C_1, one_mul] at h ⊢
  linear_combination -h

/-- Three-term recurrence, with the endpoint isolated above; no negative index. -/
theorem X_laguerre_succ (n : ℕ) :
    X * laguerre (n + 1) =
      -C ((n : ℝ) + 2) * laguerre (n + 2) +
        C (2 * (n : ℝ) + 9 / 2 + 2) * laguerre (n + 1) -
        C ((n : ℝ) + 9 / 2) * laguerre n := by
  have h0 := lowering n
  have h1 := lowering (n + 1)
  have hd := derivative_step (n + 1)
  have hx : X * (laguerre (n + 2)).derivative =
      X * (laguerre (n + 1)).derivative - X * laguerre (n + 1) := by
    simpa only [Nat.add_assoc, mul_sub] using congrArg (fun p : ℝ[X] => X * p) hd
  simp only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] at h1
  rw [h1, h0] at hx
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_1, Polynomial.C_ofNat] at hx ⊢
  linear_combination hx

end FiniteGaussianCap4.LaguerreSevenHalf
