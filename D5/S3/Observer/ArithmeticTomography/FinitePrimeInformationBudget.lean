/- GID: D5/S3/Observer/ArithmeticTomography/FinitePrimeInformationBudget
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/FinitePrimeInformationBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A complete finite prime-power budget has enough base-two information. -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.PNat.Notation
import Mathlib.Tactic

/- Library-search audit trail (2026-08-24):
   * Exact pinned-Mathlib hit `Real.logb_le_logb` transports the public
     prime-power product bound through the increasing base-two logarithm.
   * Exact pinned-Mathlib hits `Real.log_prod` and `Real.log_pow` expand that
     logarithm into the precision-weighted finite sum; all three hits are
     applied directly below.
   * Repository and pinned-library searches for finite prime information
     budgets and weighted base-two prime sums found no exact packaged theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ArithmeticTomography.FinitePrimeInformationBudget

/-- A finite set of primes with positive precision can separate a positive
window of size `N` only when its prime-power product, and hence its base-two
information sum, is at least `N`. -/
theorem finite_prime_information_budget
    (primes : Finset Nat.Primes) (precision : Nat.Primes → ℕ+) (N : Nat)
    (hN : 0 < N)
    (hcomplete : N ≤ ∏ p ∈ primes, p.1 ^ (precision p).1) :
    Real.logb 2 N ≤
      ∑ p ∈ primes, ((precision p).1 : Real) * Real.logb 2 p.1 := by
  have hfactor_pos : ∀ p ∈ primes, 0 < (p.1 : Real) ^ (precision p).1 := by
    intro p hp
    exact pow_pos (by exact_mod_cast p.2.pos) _
  have hproduct_pos : 0 < ∏ p ∈ primes, (p.1 : Real) ^ (precision p).1 := by
    exact Finset.prod_pos hfactor_pos
  have hN_real : 0 < (N : Real) := by
    exact_mod_cast hN
  have hcomplete_real :
      (N : Real) ≤ ∏ p ∈ primes, (p.1 : Real) ^ (precision p).1 := by
    exact_mod_cast hcomplete
  have hlog_bound :
      Real.logb 2 N ≤
        Real.logb 2 (∏ p ∈ primes, (p.1 : Real) ^ (precision p).1) :=
    (Real.logb_le_logb (b := 2) (by norm_num) hN_real hproduct_pos).2
      hcomplete_real
  calc
    Real.logb 2 N ≤
        Real.logb 2 (∏ p ∈ primes, (p.1 : Real) ^ (precision p).1) :=
      hlog_bound
    _ = (Real.log (∏ p ∈ primes, (p.1 : Real) ^ (precision p).1)) /
        Real.log 2 := rfl
    _ = (∑ p ∈ primes, Real.log ((p.1 : Real) ^ (precision p).1)) /
        Real.log 2 := by
      rw [Real.log_prod]
      exact fun p hp => (hfactor_pos p hp).ne'
    _ = (∑ p ∈ primes, ((precision p).1 : Real) * Real.log p.1) /
        Real.log 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      exact Real.log_pow p.1 (precision p).1
    _ = ∑ p ∈ primes, ((precision p).1 : Real) * Real.logb 2 p.1 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Real.logb]
      ring

#print axioms finite_prime_information_budget

end D5.S3.Observer.ArithmeticTomography.FinitePrimeInformationBudget
