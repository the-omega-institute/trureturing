/- GID: D5/S3/Analytic/PrimeProducts/DistinctPrimeFactorCountBound
   generality: G
   mirror-B: D5/B/S3/Analytic/PrimeProducts/DistinctPrimeFactorCountBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct prime factors are bounded by the radical and floor base-two logarithm. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Radical.NatInt

/- Library-search audit trail (2026-08-25):
   * D5 searches for blind-prime counts, distinct-prime-factor logarithmic
     bounds, and radical product bounds found no exact declaration.
   * Exact pinned-Mathlib hits `ArithmeticFunction.cardDistinctFactors_apply`
     and `List.card_toFinset` identify omega with the cardinality of the prime
     factor finset. `Finset.pow_card_le_prod` gives the lower product bound;
     `Nat.radical_eq_prod_primeFactors` and `Nat.radical_le_self_iff` give the
     upper bound; `Nat.le_log_of_pow_le` gives the floor logarithmic bound. No
     library theorem packages all three public clauses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.PrimeProducts.DistinctPrimeFactorCountBound

open scoped ArithmeticFunction.omega

/-- For a nonzero integer difference, the product of its distinct prime factors
lies between two to the number of those factors and its absolute value. Hence
the number of distinct prime factors is at most the floor base-two logarithm of
the absolute value. -/
theorem distinct_prime_factor_count_bound (d : Int) (hd : d ≠ 0) :
    2 ^ ω d.natAbs ≤ ∏ p ∈ d.natAbs.primeFactors, p ∧
      (∏ p ∈ d.natAbs.primeFactors, p) ≤ d.natAbs ∧
      ω d.natAbs ≤ Nat.log 2 d.natAbs := by
  have nonzero : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd
  have omegaCard : ω d.natAbs = d.natAbs.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply,
      ← List.card_toFinset, Nat.toFinset_factors]
  have lower : 2 ^ ω d.natAbs ≤
      ∏ p ∈ d.natAbs.primeFactors, p := by
    rw [omegaCard]
    exact Finset.pow_card_le_prod d.natAbs.primeFactors id 2 fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
  have upper : (∏ p ∈ d.natAbs.primeFactors, p) ≤ d.natAbs := by
    rw [← Nat.radical_eq_prod_primeFactors]
    exact Nat.radical_le_self_iff.mpr nonzero
  refine ⟨lower, upper, ?_⟩
  exact Nat.le_log_of_pow_le (by decide : 1 < 2) (lower.trans upper)

#print axioms distinct_prime_factor_count_bound

end D5.S3.Analytic.PrimeProducts.DistinctPrimeFactorCountBound
