/- GID: D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative
   generality: G
   mirror-B: D5/B/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Schulte's A322327 exponent-product multiplicativity conjecture. -/
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.SchulteExponentProductOmegaPowerMultiplicative

open ArithmeticFunction
open scoped ArithmeticFunction.omega

/-- A005361(n) times k to the omega(n): the product of the prime-factorization
exponents times k to the number of distinct primes. At n = 1, `a k 1 = 1` by
the empty product. -/
def a (k : ℤ) (n : ℕ) : ℤ :=
  (∏ p ∈ n.primeFactors, (n.factorization p : ℤ)) * k ^ ω n

/-- Schulte's conjecture: coprime multiplicativity and the prime-power values
`k * e` for every integer parameter k. -/
theorem result (k : ℤ) :
    (∀ m n : ℕ, m.Coprime n → a k (m * n) = a k m * a k n) ∧
    (∀ p e : ℕ, p.Prime → 0 < e → a k (p ^ e) = k * e) := by
  constructor
  · intro m n hmn
    have hprod :
        (∏ p ∈ (m * n).primeFactors, ((m * n).factorization p : ℤ)) =
          (∏ p ∈ m.primeFactors, (m.factorization p : ℤ)) *
            (∏ p ∈ n.primeFactors, (n.factorization p : ℤ)) := by
      change (m * n).factorization.prod (fun _ e => (e : ℤ)) =
        m.factorization.prod (fun _ e => (e : ℤ)) *
          n.factorization.prod (fun _ e => (e : ℤ))
      rw [Nat.factorization_mul_of_coprime hmn]
      exact Finsupp.prod_add_index_of_disjoint
        (f1 := m.factorization) (f2 := n.factorization) hmn.disjoint_primeFactors
        (fun _ e => (e : ℤ))
    dsimp only [a]
    rw [hprod, cardDistinctFactors_mul hmn, pow_add]
    exact mul_mul_mul_comm _ _ _ _
  · intro p e hp he
    simp only [a, Nat.primeFactors_prime_pow he.ne' hp, Finset.prod_singleton,
      Nat.factorization_pow_self hp, cardDistinctFactors_apply_prime_pow hp he.ne', pow_one]
    exact mul_comm _ _

end D5.S3.Arith.SchulteExponentProductOmegaPowerMultiplicative
