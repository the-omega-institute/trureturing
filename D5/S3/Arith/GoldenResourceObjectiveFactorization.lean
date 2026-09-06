/- GID: D5/S3/Arith/GoldenResourceObjectiveFactorization
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResourceObjectiveFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The resource objective at any real price decomposes into prime-direction terms. -/

import D5.S3.Arith.GoldenLocalThreshold

/- Library-search audit trail (2026-09-06):
   * Repository searches for `goldenResourceObjective`, `goldenPrimeLocalObjective`, and the
     proposed theorem names found no public arbitrary-price factorization. The only matching
     decomposition is the private `objective_factorization`/`objective_sum_on` pair at price
     1/25 in `GoldenResourceOptimalInteger`, so it cannot be imported as a GID.
   * Pinned Mathlib provides `ArithmeticFunction.sigma_one_apply_prime_pow`, `geom_sum_eq`,
     `ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization`, `Real.log_prod`,
     and `Real.log_nat_eq_sum_factorization`. These are used directly below; no declaration in
     the searched scope connects either golden-resource objective to the other.
   * Third-party Lean ecosystem searches through Tavily for the two golden objective names and
     for sigma/log factorization combinations found no matching declaration outside Mathlib. -/

namespace D5.S3.Arith.GoldenResourceObjectiveFactorization

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold

noncomputable section

private theorem golden_prime_local_objective_eq_log_sigma (lambda : ℝ) {p : ℕ}
    (hp : p.Prime) (a : ℕ) :
    goldenPrimeLocalObjective lambda p a =
      Real.log ((ArithmeticFunction.sigma 1 (p ^ a) : ℝ) / (p : ℝ) ^ a) -
        lambda * a * Real.log p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hg : (ArithmeticFunction.sigma 1 (p ^ a) : ℝ) / (p : ℝ) ^ a =
      (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹) := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    push_cast
    rw [geom_sum_eq hp1]
    simp only [inv_pow, pow_succ]
    field_simp
  unfold goldenPrimeLocalObjective
  rw [← hg]

/-- The resource objective is the sum of its local contributions over the prime support. -/
theorem golden_resource_objective_factorization (lambda : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    goldenResourceObjective lambda n =
      ∑ p ∈ n.primeFactors, goldenPrimeLocalObjective lambda p (n.factorization p) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hs : (ArithmeticFunction.sigma 1 n : ℝ) ≠ 0 := by
    exact_mod_cast (ArithmeticFunction.sigma_pos 1 n hn0).ne'
  rw [golden_resource_sigma_identity _ hn, Real.log_div hs hnR]
  rw [ArithmeticFunction.isMultiplicative_sigma.multiplicative_factorization _ hn0,
    Nat.cast_finsuppProd, Finsupp.prod, Nat.support_factorization]
  rw [Real.log_prod (fun p hp => by
    exact_mod_cast (ArithmeticFunction.sigma_pos 1 _
      (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne')]
  rw [Real.log_nat_eq_sum_factorization n]
  simp only [Finsupp.sum, Nat.support_factorization, ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [golden_prime_local_objective_eq_log_sigma lambda
    (Nat.prime_of_mem_primeFactors hp)]
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hsp : (ArithmeticFunction.sigma 1 (p ^ n.factorization p) : ℝ) ≠ 0 := by
    exact_mod_cast (ArithmeticFunction.sigma_pos 1 _
      (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne'
  rw [Real.log_div hsp (pow_ne_zero _ hp0), Real.log_pow]
  ring

/-- Extending the prime support by zero local contributions does not change the objective. -/
theorem golden_resource_objective_sum_on (lambda : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (s : Finset ℕ) (hsub : n.primeFactors ⊆ s) :
    goldenResourceObjective lambda n =
      ∑ p ∈ s, goldenPrimeLocalObjective lambda p (n.factorization p) := by
  rw [golden_resource_objective_factorization lambda hn]
  apply sum_subset hsub
  intro p _ hp
  have hzero : n.factorization p = 0 := by
    simpa [← Nat.support_factorization, Finsupp.mem_support_iff] using hp
  rw [hzero]
  by_cases hp1 : (p : ℝ)⁻¹ = 1 <;> simp [goldenPrimeLocalObjective, hp1]

end

end D5.S3.Arith.GoldenResourceObjectiveFactorization
