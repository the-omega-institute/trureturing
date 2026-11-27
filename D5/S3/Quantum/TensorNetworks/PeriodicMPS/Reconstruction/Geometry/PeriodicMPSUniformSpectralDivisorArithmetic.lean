/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpectralDivisorArithmetic
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpectralDivisorArithmetic
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Coefficient inequalities certify the spectral determinant throughout the integer length range. -/
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Arithmetic of the common spectral-divisor certificate

The constant coefficient in the `q` variable is equation (13) of the accompanying
certificate. The matrix replay supplies that coefficient identity for its integral
bivariate polynomial, and relates its evaluation to the literal determinant.
-/

namespace SpectralDivisorArithmetic

open Polynomial

private noncomputable def quadratic : Polynomial ℤ :=
  C 7600 * X ^ 2 - C 11800 * X + C 5259

/-- The polynomial `F` of equation (14). -/
noncomputable def octic : Polynomial ℤ :=
  C 102400000 * X ^ 8 + C 471040000 * X ^ 7 + C 1523584000 * X ^ 6 +
    C 2540806400 * X ^ 5 + C 1516865920 * X ^ 4 - C 922014528 * X ^ 3 -
    C 2046002172 * X ^ 2 - C 144316461 * X - C 354796803

/-- Equation (13), viewed as a polynomial in the length parameter `m`. -/
noncomputable def constantTerm : Polynomial ℤ :=
  -(C 20250 * (X + C 2) * quadratic * octic)

private theorem eval_quadratic (x : ℤ) :
    quadratic.eval x = 7600 * x ^ 2 - 11800 * x + 5259 := by
  simp [quadratic]

theorem eval_octic (x : ℤ) :
    octic.eval x = 102400000 * x ^ 8 + 471040000 * x ^ 7 + 1523584000 * x ^ 6 +
      2540806400 * x ^ 5 + 1516865920 * x ^ 4 - 922014528 * x ^ 3 -
      2046002172 * x ^ 2 - 144316461 * x - 354796803 := by
  simp [octic]

theorem eval_constantTerm (x : ℤ) :
    constantTerm.eval x =
      -(20250 * (x + 2) * (7600 * x ^ 2 - 11800 * x + 5259) * octic.eval x) := by
  simp [constantTerm, eval_quadratic]

/-- Equation (16), by exact Euclidean remainder at each of the 76 lengths. -/
theorem constantTerm_not_dvd_finite {m : ℕ} (h₈ : 8 ≤ m) (h₈₃ : m ≤ 83) :
    ¬ (3 : ℤ) ^ m ∣ constantTerm.eval (m : ℤ) := by
  simp only [Int.dvd_iff_emod_eq_zero, eval_constantTerm, eval_octic]
  interval_cases m <;> decide +kernel

/-- For these three lengths the constant coefficient is divisible by `3^m`.
The literal determinants at `m = 5, 6, 7` are cases for the matrix certificate. -/
theorem constantTerm_dvd_early {m : ℕ} (h₅ : 5 ≤ m) (h₇ : m ≤ 7) :
    (3 : ℤ) ^ m ∣ constantTerm.eval (m : ℤ) := by
  simp only [Int.dvd_iff_emod_eq_zero, eval_constantTerm, eval_octic]
  interval_cases m <;> decide +kernel

private theorem quadratic_bounds {x : ℤ} (hx : 3 ≤ x) :
    0 < quadratic.eval x ∧ quadratic.eval x < 7600 * x ^ 2 := by
  rw [eval_quadratic]
  have hlead : 0 < (7600 * x - 11800) * x :=
    mul_pos (by linarith) (by omega)
  constructor <;> linarith

private theorem octic_bounds {x : ℤ} (hx : 3 ≤ x) :
    0 < octic.eval x ∧ octic.eval x ≤ 9621826284 * x ^ 8 := by
  have hx₁ : 1 ≤ x := by omega
  have h₁₃ : x ≤ x ^ 3 := le_self_pow₀ hx₁ (by decide)
  have h₂₃ : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx₁ (by decide)
  have h₀₃ : 1 ≤ x ^ 3 := one_le_pow₀ hx₁
  have h₃ : 0 < x ^ 3 := by positivity
  have hlead : (3 : ℤ) ^ 5 * x ^ 3 ≤ x ^ 8 := by
    calc
      (3 : ℤ) ^ 5 * x ^ 3 ≤ x ^ 5 * x ^ 3 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by decide) hx 5) h₃.le
      _ = x ^ 8 := (pow_add x 5 3).symm
  have hneg : 922014528 * x ^ 3 + 2046002172 * x ^ 2 + 144316461 * x +
      354796803 ≤ 3467129964 * x ^ 3 := by
    linarith only [h₁₃, h₂₃, h₀₃]
  have h₄ : 0 ≤ x ^ 4 := by positivity
  have h₅ : 0 ≤ x ^ 5 := by positivity
  have h₆ : 0 ≤ x ^ 6 := by positivity
  have h₇ : 0 ≤ x ^ 7 := by positivity
  rw [eval_octic]
  constructor
  · linarith only [hlead, hneg, h₃, h₄, h₅, h₆, h₇]
  · have h₄₈ : x ^ 4 ≤ x ^ 8 := pow_le_pow_right₀ hx₁ (by decide)
    have h₅₈ : x ^ 5 ≤ x ^ 8 := pow_le_pow_right₀ hx₁ (by decide)
    have h₆₈ : x ^ 6 ≤ x ^ 8 := pow_le_pow_right₀ hx₁ (by decide)
    have h₇₈ : x ^ 7 ≤ x ^ 8 := pow_le_pow_right₀ hx₁ (by decide)
    have hx₀ : 0 ≤ x := by omega
    have h₂ : 0 ≤ x ^ 2 := by positivity
    have h₈ : 0 ≤ x ^ 8 := by positivity
    linarith only [h₄₈, h₅₈, h₆₈, h₇₈, hx₀, h₂, h₃, h₈]

/-- Equation (17), the degree-eleven bound on the nonzero constant coefficient. -/
theorem constantTerm_abs_bound {x : ℤ} (hx : 3 ≤ x) :
    0 < |constantTerm.eval x| ∧ |constantTerm.eval x| < 3000000000000000000 * x ^ 11 := by
  obtain ⟨hqpos, hqbound⟩ := quadratic_bounds hx
  obtain ⟨hfpos, hfbound⟩ := octic_bounds hx
  have hxpos : 0 < x := by omega
  have hfactor : x + 2 ≤ 2 * x := by omega
  have hpos : 0 < 20250 * (x + 2) * quadratic.eval x * octic.eval x := by positivity
  rw [constantTerm, eval_neg, eval_mul, eval_mul, eval_mul, eval_C, eval_add, eval_X, eval_C,
    abs_neg, abs_of_pos hpos]
  refine ⟨hpos, ?_⟩
  calc
    20250 * (x + 2) * quadratic.eval x * octic.eval x
        ≤ 20250 * (2 * x) * (7600 * x ^ 2) * (9621826284 * x ^ 8) := by
          gcongr
    _ = 2961598130215200000 * x ^ 11 := by ring
    _ < 3000000000000000000 * x ^ 11 := mul_lt_mul_of_pos_right (by decide) (by positivity)

private theorem succ_pow_lt {x : ℤ} (hx : 84 ≤ x) : (x + 1) ^ 11 < 3 * x ^ 11 := by
  have hxpos : 0 < x := by omega
  -- Cross-multiply the comparison of successive-length ratios at `x` and at `84`.
  have hcross : 84 * (x + 1) ≤ 85 * x := by linarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 84 * (x + 1)) hcross 11
  simp only [mul_pow] at hpow
  have hnum : (85 : ℤ) ^ 11 < 3 * 84 ^ 11 := by decide +kernel
  apply lt_of_mul_lt_mul_left (a := (84 : ℤ) ^ 11) _ (by positivity)
  calc
    84 ^ 11 * (x + 1) ^ 11 ≤ 85 ^ 11 * x ^ 11 := hpow
    _ < (3 * 84 ^ 11) * x ^ 11 := mul_lt_mul_of_pos_right hnum (by positivity)
    _ = 84 ^ 11 * (3 * x ^ 11) := by ring

private theorem pow_bound {m : ℕ} (hm : 84 ≤ m) :
    3000000000000000000 * (m : ℤ) ^ 11 < (3 : ℤ) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    have hm' : (84 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    rw [Nat.cast_succ, pow_succ (3 : ℤ)]
    calc
      3000000000000000000 * ((m : ℤ) + 1) ^ 11
          < 3000000000000000000 * (3 * (m : ℤ) ^ 11) :=
            mul_lt_mul_of_pos_left (succ_pow_lt hm') (by decide)
      _ = (3000000000000000000 * (m : ℤ) ^ 11) * 3 := by ring
      _ < (3 : ℤ) ^ m * 3 := mul_lt_mul_of_pos_right ih (by decide)

/-- Equation (18), strict exponential domination starting at length 84. -/
theorem constantTerm_abs_lt_pow {m : ℕ} (hm : 84 ≤ m) :
    0 < |constantTerm.eval (m : ℤ)| ∧ |constantTerm.eval (m : ℤ)| < (3 : ℤ) ^ m := by
  have hm' : (3 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (show 3 ≤ m by omega)
  obtain ⟨hpos, hbound⟩ := constantTerm_abs_bound hm'
  exact ⟨hpos, hbound.trans (pow_bound hm)⟩

/-- The constant coefficient is never divisible by `3^m` for `m ≥ 8`. -/
theorem constantTerm_not_dvd {m : ℕ} (hm : 8 ≤ m) :
    ¬ (3 : ℤ) ^ m ∣ constantTerm.eval (m : ℤ) := by
  by_cases hfin : m ≤ 83
  · exact constantTerm_not_dvd_finite hm hfin
  · obtain ⟨hpos, hlt⟩ := constantTerm_abs_lt_pow (m := m) (by omega)
    intro hdvd
    have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg _) hlt ((dvd_abs _ _).mpr hdvd)
    exact hpos.ne' hzero

/-- After substituting `q = (-3)^m`, the constant coefficient determines the
residue of every integral bivariate polynomial modulo `3^m`. The outer variable is `q`. -/
theorem pow_dvd_evalEval_sub_constantCoeff (N : Polynomial (Polynomial ℤ)) (m : ℕ) :
    (3 : ℤ) ^ m ∣ N.evalEval (m : ℤ) ((-3 : ℤ) ^ m) - (N.coeff 0).eval (m : ℤ) := by
  have hpoly : C ((-3 : ℤ) ^ m) ∣ N.eval (C ((-3 : ℤ) ^ m)) - N.coeff 0 := by
    simpa only [sub_zero, coeff_zero_eq_eval_zero] using
      sub_dvd_eval_sub (C ((-3 : ℤ) ^ m)) 0 N
  have hsign : (3 : ℤ) ^ m ∣ (-3 : ℤ) ^ m :=
    pow_dvd_pow_of_dvd (by decide : (3 : ℤ) ∣ -3) m
  apply hsign.trans
  simpa only [coe_evalRingHom, eval_C, eval_sub, evalEval] using
    (map_dvd (evalRingHom (m : ℤ)) hpoly)

/-- Equations (13) and (15) imply nonvanishing for any integral `N(m,q)` with
that `q`-constant coefficient. The equality `N.coeff 0 = constantTerm` is the
interface to the determinant coefficient computation. -/
theorem evalEval_ne_zero (N : Polynomial (Polynomial ℤ)) (hN : N.coeff 0 = constantTerm)
    {m : ℕ} (hm : 8 ≤ m) : N.evalEval (m : ℤ) ((-3 : ℤ) ^ m) ≠ 0 := by
  intro hzero
  apply constantTerm_not_dvd hm
  simpa [hN, hzero] using pow_dvd_evalEval_sub_constantCoeff N m

end SpectralDivisorArithmetic
