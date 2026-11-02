/- GID: D5/S3/ArithSums/HannaLaurentFirstMoment
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaLaurentFirstMoment
   mirror-E: none(waiver:symbolic-laurent-coefficient-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Derivative]
   utility: none
   digest: The first weighted moment of every positive A391810 Laurent row equals one. -/

import D5.S3.ArithSums.HannaLaurentRowSums
import Mathlib.Algebra.Polynomial.Derivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.HannaLaurentFirstMoment

open scoped BigOperators
open D5.S3.ArithSums.HannaLaurentRowSums

noncomputable section

private theorem derivative_at_one (n : ℕ) (hn : 0 < n) :
    (rowPolynomial n).derivative.eval 1 = (1 : ℤ) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => norm_num [rowPolynomial]
    | succ m =>
      have hz : ∀ j ∈ Finset.range m,
          ((Polynomial.X ^ (j + 1) *
            (1 - Polynomial.X ^ (j + 1)) ^ (m + 2 - (j + 1)) :
              Polynomial ℤ).derivative).eval 1 = 0 := by
        intro j hj
        have hjm := Finset.mem_range.mp hj
        have he : m + 1 - j ≠ 0 := by omega
        have he' : m + 1 - j - 1 ≠ 0 := by omega
        simp [Polynomial.derivative_mul, Polynomial.derivative_pow,
          Polynomial.derivative_sub, he, he']
      change (rowPolynomial (m + 2)).derivative.eval 1 = 1
      simp only [rowPolynomial, Polynomial.derivative_add, Polynomial.derivative_neg,
        Polynomial.derivative_one, neg_zero, zero_add, Polynomial.derivative_sum,
        Polynomial.eval_finsetSum]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [Finset.sum_eq_zero hz]
      simp [Polynomial.derivative_mul, Polynomial.derivative_pow,
        Polynomial.derivative_sub]
      ring

private theorem integer_moment (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (rowBound n + 1), (k : ℤ) * rowEntry n k = 1 := by
  have h := Polynomial.derivative_eval (rowPolynomial n) (1 : ℤ)
  rw [Polynomial.sum_over_range' _ (by simp) (rowBound n + 1)
    (Nat.lt_succ_of_le (row_degree n))] at h
  simpa [rowEntry, one_pow, mul_comm] using h.symm.trans (derivative_at_one n hn)

/-- Formula (3) of A391810, in integer entries and literal bilateral Laurent coefficients. -/
theorem result (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range (rowBound n + 1), (k : ℤ) * rowEntry n k = 1) ∧
    (∑ k ∈ Finset.range (rowBound n + 1),
      (k : ℚ) * (series n hn).coeff (-(k : ℤ)) = 1) := by
  refine ⟨integer_moment n hn, ?_⟩
  simp_rw [series_coefficient]
  have h := integer_moment n hn
  exact_mod_cast h

end
end D5.S3.ArithSums.HannaLaurentFirstMoment
