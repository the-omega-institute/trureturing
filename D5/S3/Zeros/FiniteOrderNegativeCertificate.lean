/- GID: D5/S3/Zeros/FiniteOrderNegativeCertificate
   generality: G
   mirror-B: D5/B/S3/Zeros/FiniteOrderNegativeCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A zero weighted positive-order sum has a negative coefficient and a sharp witness. -/

import Mathlib

/- Library-search audit trail (2026-09-04):
   * Repository searches for finite-order negative certificates, zero weighted
     sums, and more general nonnegative-series obstructions found no owner of
     this statement.
   * `Summable.tsum_pos` is the pinned Mathlib result that turns one strictly
     positive summand in a nonnegative summable family into a positive total.
   * The source's appeal to a nonzero entire function supplies nontriviality of
     the coefficients. Since that analytic carrier is absent from the atom, the
     necessary nontriviality premise is stated explicitly rather than assumed
     through an unformalized identity theorem argument.
   * Positive orders are represented as `n + 1`, so order zero cannot silently
     contribute to or cancel the displayed series. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.FiniteOrderNegativeCertificate

open scoped BigOperators

/-- If a nontrivial family on the positive integer orders has positive weights,
is summable, and has zero weighted sum, then some finite-order coefficient is
negative. -/
theorem exists_finite_order_negative_certificate
    (J weight : ℕ -> ℝ)
    (weight_pos : ∀ n, 0 < weight (n + 1))
    (weighted_summable : Summable (fun n => weight (n + 1) * J (n + 1)))
    (weighted_sum_zero : (∑' n, weight (n + 1) * J (n + 1)) = 0)
    (nontrivial : ∃ n, J (n + 1) ≠ 0) :
    ∃ m, 1 ≤ m ∧ J m < 0 := by
  by_contra no_negative
  push Not at no_negative
  obtain ⟨n, hn⟩ := nontrivial
  have J_nonneg : ∀ k, 0 ≤ J (k + 1) := by
    intro k
    exact no_negative (k + 1) (by omega)
  have J_pos : 0 < J (n + 1) :=
    lt_of_le_of_ne (J_nonneg n) (Ne.symm hn)
  have total_pos : 0 < ∑' k, weight (k + 1) * J (k + 1) :=
    weighted_summable.tsum_pos
      (fun k => mul_nonneg (weight_pos k).le (J_nonneg k))
      n
      (mul_pos (weight_pos n) J_pos)
  rw [weighted_sum_zero] at total_pos
  exact lt_irrefl 0 total_pos

/-- The hypotheses are jointly satisfiable and the conclusion is sharp: unit
weights with `J 1 = -1` and `J 2 = 1` have exactly zero weighted sum. -/
theorem two_term_zero_sum_witness :
    ∃ J weight : ℕ -> ℝ,
      (∀ n, 0 < weight (n + 1)) ∧
      Summable (fun n => weight (n + 1) * J (n + 1)) ∧
      (∑' n, weight (n + 1) * J (n + 1)) = 0 ∧
      J 1 = -1 ∧ J 2 = 1 := by
  let J : ℕ -> ℝ := fun m => if m = 1 then -1 else if m = 2 then 1 else 0
  let weight : ℕ -> ℝ := fun _ => 1
  refine ⟨J, weight, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp [weight]
  · apply summable_of_ne_finset_zero (s := {0, 1})
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    obtain ⟨hn_zero, hn_one⟩ := not_or.mp hn
    simp [J, weight, hn_zero, hn_one]
  · rw [tsum_eq_sum (s := {0, 1})]
    · norm_num [J, weight]
    · intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      obtain ⟨hn_zero, hn_one⟩ := not_or.mp hn
      simp [J, weight, hn_zero, hn_one]
  · simp [J]
  · simp [J]

#print axioms exists_finite_order_negative_certificate
#print axioms two_term_zero_sum_witness

end D5.S3.Zeros.FiniteOrderNegativeCertificate
