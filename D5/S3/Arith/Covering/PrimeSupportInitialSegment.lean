/- GID: D5/S3/Arith/Covering/PrimeSupportInitialSegment
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/PrimeSupportInitialSegment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Minimal odd covers contain the product of every smaller odd prime in their common modulus. -/

import D5.S3.Arith.Covering.PrimeSupportGapDescent
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos7.OddDistinctCoveringSystem

open scoped BigOperators

variable {L : ℕ}

/-- The odd primes below `q` form a finite support prefix. -/
def oddPrimeBelow (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun p => p.Prime ∧ Odd p)

/-- In a count-then-sum minimal odd distinct cover, a prime in the common
modulus forces every smaller odd prime into that common modulus.  The product
statement packages these pairwise coprime divisibilities into one usable
boundary condition. -/
theorem odd_prime_product_dvd_commonModulus
    (F : OddDistinctCoveringSystem L)
    (hcountMin : ∀ {N : ℕ}, OddDistinctCoveringSystem N → L ≤ N)
    (hsumMin : ∀ H : OddDistinctCoveringSystem L,
      (∑ i, F.modulus i) ≤ ∑ i, H.modulus i)
    (q : ℕ) (hq : Nat.Prime q) (hqPresent : q ∣ F.commonModulus) :
    (∏ p ∈ oddPrimeBelow q, p) ∣ F.commonModulus := by
  classical
  have prod_dvd : ∀ s : Finset ℕ,
      (∀ p ∈ s, Nat.Prime p) →
      (∀ p r, p ∈ s → r ∈ s → p ≠ r → Nat.Coprime p r) →
      (∀ p ∈ s, p ∣ F.commonModulus) →
          (∏ p ∈ s, p) ∣ F.commonModulus := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _ _ _
        simp
    | @insert a s ha ih =>
        intro hprime hpair hdvd
        rw [Finset.prod_insert ha]
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        · apply Nat.Coprime.prod_right
          intro p hp
          apply (Nat.coprime_primes (hprime a (by simp))
            (hprime p (Finset.mem_insert_of_mem hp))).2
          intro hap
          subst p
          exact ha hp
        · exact hdvd a (by simp)
        · apply ih
          · intro p hp
            exact hprime p (Finset.mem_insert_of_mem hp)
          · intro p r hp hr hpr
            exact hpair p r (Finset.mem_insert_of_mem hp)
              (Finset.mem_insert_of_mem hr) hpr
          · intro p hp
            exact hdvd p (Finset.mem_insert_of_mem hp)
  apply prod_dvd
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  · intro p r hp hr hpr
    exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2.1
      (Finset.mem_filter.mp hr).2.1).2 hpr
  · intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hpprime : Nat.Prime p := hmem.2.1
    have hpodd : Odd p := hmem.2.2
    have hpq : p < q := Finset.mem_range.mp hmem.1
    by_contra hpAbsent
    exact no_gap_in_prime_support F hcountMin hsumMin p q hpprime hq hpodd hpq
      hpAbsent hqPresent |>.elim

end Erdos7.OddDistinctCoveringSystem
