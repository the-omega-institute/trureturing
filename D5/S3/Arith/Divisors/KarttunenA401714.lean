/- GID: D5/S3/Arith/Divisors/KarttunenA401714
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/KarttunenA401714
   mirror-E: none(waiver:unbounded-symbolic-divisor-sum-implication)
   anchors: []
   utility: none
   digest: The radical quotient condition implies the joint divisor-sum inequality. -/

import D5.S3.Arith.Divisors.UnitaryProductBridge
import Mathlib.Data.Nat.Prime.Infinite

/-! # Karttunen's unitary and squarefree divisor-sum implication -/

namespace D5.S3.Arith.Divisors.KarttunenA401714

open D5.S3.Arith.EulerFormDivisorSum

private theorem missing_prime_exists (N : ℕ) (hn : 0 < N) :
    ∃ p : ℕ, Nat.Prime p ∧ ¬ p ∣ N := by
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 1)
  exact ⟨p, hp, fun hd => by have := Nat.le_of_dvd hn hd; omega⟩

/-- The least prime not dividing a positive integer. -/
def leastMissingPrime (N : ℕ) (hn : 0 < N) : ℕ :=
  Nat.find (missing_prime_exists N hn)

/-- The full A401714/A401715 implication, for every positive integer. -/
theorem result (N : ℕ) (hn : 0 < N)
    (hmissing : N / (∏ p ∈ N.primeFactors, p) < leastMissingPrime N hn) :
    2 * N ≤ unitarySum N + squarefreeSum N := by
  apply UnitaryProductBridge.unitary_squarefree_ge_twice_of_support N hn.ne'
  intro p hp hpm
  by_contra hpd
  have hq : leastMissingPrime N hn ≤ p :=
    Nat.find_min' (missing_prime_exists N hn) ⟨hp, hpd⟩
  omega

end D5.S3.Arith.Divisors.KarttunenA401714
