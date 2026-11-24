/- GID: D5/S3/Arith/PrimitiveRoot/ChebyshevThirty
   generality: G
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/ChebyshevThirty
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: The Chebyshev factorial combination gives an unconditional linear psi lower bound. -/

import D5.S3.Arith.LogConvolutionMassExpansion
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The factorial combination uses the scales 1, 1/30, 1/2, 1/3 and 1/5. -/

namespace D5.S3.Arith.PrimitiveRoot.ChebyshevThirty

open scoped BigOperators ArithmeticFunction
open Finset
open D5.S3.Arith.LogConvolutionMassExpansion

/-- The coefficient in Chebyshev's thirty-period factorial comparison. -/
noncomputable def coefficient : ℝ :=
  Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30

private theorem floor_combination (n : ℕ) :
    n + n / 30 ≤ 1 + n / 2 + n / 3 + n / 5 := by
  omega

private theorem log_factorial_sum (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d * (n / d : ℕ) := by
  rw [← sum_log_eq_log_factorial]
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.vonMangoldt) n
  simpa using h

private theorem log_factorial_sum_extended (m n : ℕ) (hmn : m ≤ n) :
    Real.log (m.factorial : ℝ) =
      ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d * (m / d : ℕ) := by
  rw [log_factorial_sum]
  apply Finset.sum_subset (Ioc_subset_Ioc_right hmn)
  intro d hd hn
  have hmd : m < d := by
    simp only [mem_Ioc, not_and] at hn
    exact lt_of_not_ge (hn (mem_Ioc.mp hd).1)
  simp [Nat.div_eq_of_lt hmd]

/-- Chebyshev's log-factorial combination is bounded by the full Mangoldt prefix. -/
private theorem factorial_combination_le_psi (n : ℕ) :
    Real.log (n.factorial : ℝ) + Real.log ((n / 30).factorial : ℝ) -
      Real.log ((n / 2).factorial : ℝ) - Real.log ((n / 3).factorial : ℝ) -
      Real.log ((n / 5).factorial : ℝ) ≤ Chebyshev.psi n := by
  rw [log_factorial_sum n,
    log_factorial_sum_extended (n / 30) n (Nat.div_le_self _ _),
    log_factorial_sum_extended (n / 2) n (Nat.div_le_self _ _),
    log_factorial_sum_extended (n / 3) n (Nat.div_le_self _ _),
    log_factorial_sum_extended (n / 5) n (Nat.div_le_self _ _),
    Chebyshev.psi, Nat.floor_natCast]
  rw [← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_le_sum
  intro d hd
  have hdiv (k : ℕ) : n / k / d = n / d / k := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k d]
  rw [hdiv 30, hdiv 2, hdiv 3, hdiv 5]
  have hb : ((n / d : ℕ) : ℝ) + (n / d / 30 : ℕ) - (n / d / 2 : ℕ) -
      (n / d / 3 : ℕ) - (n / d / 5 : ℕ) ≤ 1 := by
    have hb := floor_combination (n / d)
    have hbR : ((n / d : ℕ) : ℝ) + (n / d / 30 : ℕ) ≤
        1 + (n / d / 2 : ℕ) + (n / d / 3 : ℕ) + (n / d / 5 : ℕ) := by
      exact_mod_cast hb
    linarith
  have hh := mul_le_mul_of_nonneg_left hb
    (ArithmeticFunction.vonMangoldt_nonneg (n := d))
  push_cast
  push_cast at hh
  nlinarith

private theorem factorial_error_scaled (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    |Real.log ((n / k).factorial : ℝ) -
      ((n : ℝ) / k * Real.log ((n : ℝ) / k) - (n : ℝ) / k)| ≤
        1 + Real.log n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h := floor_factorial_log_error ((n : ℝ) / k) n
    (by positivity) (by apply div_le_self (by positivity) hkR) hnR
  simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using h

/-- The explicit unconditional Chebyshev lower estimate at every positive integer. -/
theorem psi_nat_lower (n : ℕ) (hn : 1 ≤ n) :
    coefficient * n - 5 * (1 + Real.log n) ≤ Chebyshev.psi n := by
  have h1 := factorial_error_scaled n 1 hn (by norm_num)
  have h30 := factorial_error_scaled n 30 hn (by norm_num)
  have h2 := factorial_error_scaled n 2 hn (by norm_num)
  have h3 := factorial_error_scaled n 3 hn (by norm_num)
  have h5 := factorial_error_scaled n 5 hn (by norm_num)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [Nat.div_one, Nat.cast_one, div_one] at h1
  norm_num only [Nat.cast_ofNat] at h30 h2 h3 h5
  rw [Real.log_div hn0 (by norm_num)] at h30 h2 h3 h5
  rw [abs_le] at h1 h30 h2 h3 h5
  have hh := factorial_combination_le_psi n
  dsimp only [coefficient]
  nlinarith [h1.1, h30.1, h2.2, h3.2, h5.2]

/-- Rational bounds on the exact logarithmic coefficient. -/
theorem coefficient_bounds : (921 / 1000 : ℝ) ≤ coefficient ∧ coefficient ≤ 1 := by
  have he : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  dsimp only [coefficient]
  rw [he]
  constructor
  · linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  · linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

#print axioms psi_nat_lower
#print axioms coefficient_bounds

end D5.S3.Arith.PrimitiveRoot.ChebyshevThirty
