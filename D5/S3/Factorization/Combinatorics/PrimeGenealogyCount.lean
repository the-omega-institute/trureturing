/- GID: D5/S3/Factorization/Combinatorics/PrimeGenealogyCount
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/PrimeGenealogyCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct prime-factor orderings equal the multinomial of their multiplicities. -/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorization.Basic

namespace D5.S3.Factorization.Combinatorics.PrimeGenealogyCount

/-- The number of ordered prime-factor genealogies of `n`: each ordering of the canonical
prime-factor multiset is counted once. -/
noncomputable def primeGenealogyCount (n : ℕ) : ℕ :=
  Multiset.countPerms (n.primeFactorsList : Multiset ℕ)

/-- The genealogy count is the factorial of the total prime multiplicity divided by the
product of the factorials of the individual prime multiplicities. -/
theorem prime_genealogy_count_formula (n : ℕ) :
    primeGenealogyCount n =
      Nat.factorial (n.factorization.sum fun _ => id) /
        n.factorization.prod fun _ exponent => Nat.factorial exponent := by
  rw [primeGenealogyCount, Multiset.countPerms, Finsupp.multinomial,
    ← Nat.factorization_eq_primeFactorsList_multiset]

#print axioms prime_genealogy_count_formula

end D5.S3.Factorization.Combinatorics.PrimeGenealogyCount
