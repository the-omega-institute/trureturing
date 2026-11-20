/- GID: D5/S3/Analytic/HalfIntegerBesselPolynomial
   generality: G
   mirror-B: D5/B/S3/Analytic/HalfIntegerBesselPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normalized Bessel polynomials and their reflected Wronskian. -/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Half-integer Bessel polynomials

The coefficients use the normalization of DLMF 10.17.1. The indeterminate is the
reciprocal argument in the finite half-integer carriers of DLMF 10.49.8 and 10.49.12.
-/

public section

open Polynomial
open scoped Nat

namespace D5.S3.Analytic.HalfIntegerBesselPolynomial

/-- The normalized coefficient, extended by zero past the degree. -/
def coefficient (m k : ℕ) : ℚ :=
  if k ≤ m then ((m + k)! : ℚ) / (2 ^ k * (k ! : ℚ) * ((m - k)! : ℚ)) else 0

/-- The polynomial evaluated at the reciprocal argument of the decaying carrier. -/
def carrier (m : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (m + 1), monomial k (coefficient m k)

private theorem coefficient_zero (m : ℕ) : coefficient m 0 = 1 := by
  simp [coefficient, Nat.factorial_ne_zero]

/-- The recurrence holds at the last coefficient and throughout the zero extension. -/
theorem coefficient_succ (m k : ℕ) :
    2 * ((k : ℚ) + 1) * coefficient m (k + 1) =
      ((m : ℚ) - k) * (m + (k : ℚ) + 1) * coefficient m k := by
  by_cases h : k < m
  · have hs : k + 1 ≤ m := h
    have hsub : m - k = (m - (k + 1)) + 1 := by omega
    have hcast : (↑(m - (k + 1)) : ℚ) + 1 = (m : ℚ) - k := by
      rw [← Nat.cast_one, ← Nat.cast_add, ← hsub, Nat.cast_sub h.le]
    rw [coefficient, if_pos hs, coefficient, if_pos h.le]
    rw [show m + (k + 1) = m + k + 1 by omega, hsub]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    rw [hcast]
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    have hmk : (m : ℚ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h.ne')
    have hfact (j : ℕ) : (j ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hpow : (2 : ℚ)^k ≠ 0 := by positivity
    field_simp
    <;> ring
  · rw [coefficient, if_neg (by omega)]
    rcases (le_of_not_gt h).eq_or_lt with heq | hlt
    · subst m
      simp
    · simp [coefficient, not_le.mpr hlt]

private theorem coeff_carrier (m k : ℕ) : (carrier m).coeff k = coefficient m k := by
  by_cases h : k ≤ m
  · simp [carrier, coeff_monomial, Finset.mem_range, Nat.lt_succ_iff, h]
  · simp [carrier, coeff_monomial, Finset.mem_range, Nat.lt_succ_iff, coefficient, h]

/-- The differential equation in the reciprocal argument. -/
theorem carrier_ode (m : ℕ) :
    X ^ 2 * (carrier m).derivative.derivative +
        (C 2 * X + C 2) * (carrier m).derivative =
      C ((m : ℚ) * (m + 1)) * carrier m := by
  have first (p : ℚ[X]) (k : ℕ) : (X * p.derivative).coeff k = p.coeff k * k := by
    cases k with
    | zero => simp
    | succ k => rw [coeff_X_mul, coeff_derivative]
  have second (p : ℚ[X]) (k : ℕ) :
      (X ^ 2 * p.derivative.derivative).coeff k = p.coeff k * k * ((k : ℚ) - 1) := by
    rcases k with _ | _ | k
    · norm_num [coeff_X_pow_mul']
    · norm_num [coeff_X_pow_mul']
    · rw [show k + 1 + 1 = k + 2 by omega, coeff_X_pow_mul]
      simp only [coeff_derivative, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      ring
  ext k
  rw [add_mul, mul_assoc, coeff_add, coeff_add, second, coeff_C_mul, first,
    coeff_C_mul, coeff_derivative, coeff_C_mul]
  simp only [coeff_carrier, Nat.cast_add, Nat.cast_one]
  linear_combination coefficient_succ m k

private theorem derivative_reflection (p : ℚ[X]) :
    (p.comp (-X)).derivative = -p.derivative.comp (-X) := by
  simp [derivative_comp]

private theorem reflected_ode (m : ℕ) :
    X ^ 2 * ((carrier m).comp (-X)).derivative.derivative +
        (C 2 * X - C 2) * ((carrier m).comp (-X)).derivative =
      C ((m : ℚ) * (m + 1)) * (carrier m).comp (-X) := by
  have h := congrArg (fun p : ℚ[X] => p.comp (-X)) (carrier_ode m)
  simp only [add_comp, mul_comp, pow_comp, C_comp, X_comp] at h
  simp only [derivative_reflection, derivative_neg, neg_neg]
  convert h using 1 <;> ring

/-- The reflected polynomial Wronskian, normalized by the constant term of the carrier. -/
theorem reflected_wronskian (m : ℕ) :
    let p := carrier m
    let q := p.comp (-X)
    C 2 * p * q - X ^ 2 * (p * q.derivative - p.derivative * q) = C 2 := by
  let p := carrier m
  let q := p.comp (-X)
  let w := C 2 * p * q - X ^ 2 * (p * q.derivative - p.derivative * q)
  change w = C 2
  have hp := carrier_ode m
  have hq := reflected_ode m
  fold p at hp
  change X ^ 2 * q.derivative.derivative + (C 2 * X - C 2) * q.derivative =
    C ((m : ℚ) * (m + 1)) * q at hq
  have hw : w.derivative = 0 := by
    simp only [w, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_X_sq]
    linear_combination q * hp - p * hq
  have hp0 : p.coeff 0 = 1 := (coeff_carrier m 0).trans (coefficient_zero m)
  have hq0 : q.coeff 0 = 1 := by
    rw [← eval_zero_eq_coeff_zero, q, eval_comp, eval_neg, eval_X, neg_zero,
      eval_zero_eq_coeff_zero, hp0]
  have hw0 : w.coeff 0 = 2 := by
    simp [w, coeff_mul_zero, coeff_X_pow_mul', hp0, hq0]
  rw [eq_C_of_derivative_eq_zero hw, hw0]

end D5.S3.Analytic.HalfIntegerBesselPolynomial
