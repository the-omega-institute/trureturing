/- GID: D5/S3/ArithSums/HannaLaurentAlternatingJacobsthal
   generality: I
   mirror-B: D5/B/S3/ArithSums/HannaLaurentAlternatingJacobsthal
   mirror-E: none(waiver:symbolic-laurent-alternating-coefficient-proof)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Round,mathlib/module/Mathlib.Algebra.Polynomial.Eval.Degree]
   utility: none
   digest: The full A391810 alternating Laurent row formula equals twice the nearest integer and twice the offset-zero Jacobsthal number. -/

import D5.S3.ArithSums.HannaLaurentRowSums
import Mathlib.Algebra.Order.Round

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
namespace D5.S3.ArithSums.HannaLaurentAlternatingJacobsthal
open D5.S3.ArithSums.HannaLaurentRowSums
noncomputable section

/-- Offset-zero Jacobsthal sequence with the published initial conditions. -/
def jacobsthal : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => jacobsthal (n + 1) + 2 * jacobsthal n

private lemma jacobsthal_closed (n : ℕ) :
    3 * jacobsthal n = (2 : ℤ)^n - (-1 : ℤ)^n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [jacobsthal]
  | one => norm_num [jacobsthal]
  | more n h0 h1 =>
    rw [jacobsthal, pow_succ, pow_succ, pow_succ, pow_succ]
    linear_combination h1 + 2 * h0

private lemma jacobsthal_skip (n : ℕ) :
    jacobsthal (n + 2) = jacobsthal n + (2 : ℤ)^n := by
  have h0 := jacobsthal_closed n
  have h2 := jacobsthal_closed (n + 2)
  simp only [pow_add, pow_two] at h2
  norm_num at h2
  linarith

private lemma jacobsthal_round (n : ℕ) :
    round ((2 : ℚ)^n / 3) = jacobsthal n := by
  apply round_eq_iff.mpr
  have hc : 3 * (jacobsthal n : ℚ) = (2 : ℚ)^n - (-1 : ℚ)^n := by
    exact_mod_cast jacobsthal_closed n
  have hp : (-1 : ℚ)^n = 1 ∨ (-1 : ℚ)^n = -1 := by
    rcases Nat.even_or_odd n with h | h
    · exact Or.inl (h.neg_one_pow)
    · exact Or.inr (h.neg_one_pow)
  constructor <;> rcases hp with hp | hp <;> rw [hp] at hc <;> linarith

private lemma polynomial_at_neg_one_skip (n : ℕ) (hn : 0 < n) :
    (rowPolynomial (n + 2)).eval (-1) =
      (rowPolynomial n).eval (-1) - (2 : ℤ)^(n + 1) := by
  simp only [rowPolynomial, Polynomial.eval_add, Polynomial.eval_neg,
    Polynomial.eval_one, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  rw [show n + 2 = 2 + n by omega, Finset.sum_range_add]
  have ht : (∑ j ∈ Finset.range n,
      (-1 : ℤ) ^ (2 + j + 1) * (1 - (-1 : ℤ) ^ (2 + j + 1)) ^ (2 + n - (2 + j + 1))) =
      ∑ j ∈ Finset.range n,
      (-1 : ℤ) ^ (j + 1) * (1 - (-1 : ℤ) ^ (j + 1)) ^ (n - (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show 2 + j + 1 = (j + 1) + 2 by omega, pow_add]
    norm_num
    congr 1
    omega
  rw [ht]
  simp [Finset.sum_range_succ, show 2 + n - 1 = n + 1 by omega,
    show 2 + n - 2 = n by omega, hn.ne']
  ring

private lemma polynomial_at_neg_one (n : ℕ) (hn : 0 < n) :
    (rowPolynomial n).eval (-1) = -2 * jacobsthal n := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one => norm_num [rowPolynomial, jacobsthal, Finset.sum_range_succ]
  | more n h0 h1 =>
    by_cases h : n = 0
    · subst n
      norm_num [rowPolynomial, jacobsthal, Finset.sum_range_succ]
    · rw [polynomial_at_neg_one_skip n (by omega), h0 (by omega), jacobsthal_skip]
      rw [pow_succ]
      ring

private lemma alternating_coefficient_bridge (n : ℕ) :
    (∑ k ∈ Finset.range (rowBound n + 1), -((-1 : ℤ)^k) * rowEntry n k) =
      -(rowPolynomial n).eval (-1) := by
  have he := Polynomial.eval_eq_sum_range' (p := rowPolynomial n)
    (Nat.lt_succ_of_le (row_degree n)) (-1 : ℤ)
  simp only [rowEntry]
  calc
    (∑ k ∈ Finset.range (rowBound n + 1), -((-1 : ℤ)^k) * (rowPolynomial n).coeff k) =
        -(∑ k ∈ Finset.range (rowBound n + 1), (rowPolynomial n).coeff k * (-1 : ℤ)^k) := by
          simp_rw [neg_mul, mul_comm]
          rw [Finset.sum_neg_distrib]
    _ = -(rowPolynomial n).eval (-1) := by rw [← he]

/-- The whole original formula (5), including its exact formal Laurent coefficients. -/
theorem full_formula_five (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (((n + 1) / 2)^2 + 1),
      -((-1 : ℤ)^k) * rowEntry n k) =
        2 * round ((2 : ℚ)^n / 3) ∧
    2 * round ((2 : ℚ)^n / 3) = 2 * jacobsthal n ∧
    (∑ k ∈ Finset.range (((n + 1) / 2)^2 + 1),
      -((-1 : ℚ)^k) * (series n (by omega)).coeff (-(k : ℤ))) =
        (2 : ℚ) * (round ((2 : ℚ)^n / 3) : ℚ) ∧
    (∀ k : ℕ, (series n (by omega)).coeff (-(k : ℤ)) = (rowEntry n k : ℚ)) ∧
    (∀ k : ℕ, ((n + 1) / 2)^2 < k →
      (series n (by omega)).coeff (-(k : ℤ)) = 0) := by
  have hJ := jacobsthal_round n
  have hrow : (∑ k ∈ Finset.range (((n + 1) / 2)^2 + 1),
      -((-1 : ℤ)^k) * rowEntry n k) = 2 * jacobsthal n := by
    change (∑ k ∈ Finset.range (rowBound n + 1), _) = _
    rw [alternating_coefficient_bridge, polynomial_at_neg_one n (by omega)]
    ring
  refine ⟨?_, by rw [hJ], ?_, ?_, ?_⟩
  · rwa [hJ]
  · simp_rw [series_coefficient]
    rw [hJ]
    exact_mod_cast hrow
  · intro k
    exact series_coefficient n (by omega) k
  · intro k hk
    rw [series_coefficient, Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (row_degree n) hk), Int.cast_zero]

end
end D5.S3.ArithSums.HannaLaurentAlternatingJacobsthal
