/- GID: D5/S3/Factorization/UniqueFactorization
   generality: G
   mirror-B: D5/B/S3/Factorization/UniqueFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime factorization of a natural number is unique up to permutation. -/

import Mathlib.Data.Nat.Factors

/- Provenance: thin honest wrapper over pinned mathlib's canonical-list
   uniqueness (`Nat.primeFactorsList_unique`); the two-list permutation
   statement is glued through the canonical factor list. -/

namespace D5.S3.Factorization.UniqueFactorization

/--
Uniqueness of prime factorization up to rearrangement: any two lists of
primes with the same product are permutations of each other.  Each list is
identified with the canonical factor list of the common product by mathlib's
`Nat.primeFactorsList_unique`, and the permutation is composed through it.
-/
theorem prime_factorization_unique {n : ℕ} {l₁ l₂ : List ℕ}
    (prime₁ : ∀ p ∈ l₁, Nat.Prime p) (value₁ : l₁.prod = n)
    (prime₂ : ∀ p ∈ l₂, Nat.Prime p) (value₂ : l₂.prod = n) :
    l₁.Perm l₂ :=
  (Nat.primeFactorsList_unique value₁ prime₁).trans
    (Nat.primeFactorsList_unique value₂ prime₂).symm

end D5.S3.Factorization.UniqueFactorization
