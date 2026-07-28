/- GID: D5/S3/Arith/PrimeFactorization
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every natural number greater than one is a product of finitely many primes. -/

import Mathlib.Data.Nat.Factors

namespace D5.S3.Arith.PrimeFactorization

/-- Existence of prime factorization: every natural number greater than one is
the product of a finite list of prime numbers. -/
theorem exists_prime_factorization {n : ℕ} (hn : 1 < n) :
    ∃ l : List ℕ, (∀ p ∈ l, Nat.Prime p) ∧ l.prod = n :=
  ⟨n.primeFactorsList,
    fun _ hp => Nat.prime_of_mem_primeFactorsList hp,
    Nat.prod_primeFactorsList (by omega)⟩

end D5.S3.Arith.PrimeFactorization
