/- GID: D5/S3/Arith/DivisorGibbs/FullWindowDivisorBridge
   generality: I
   mirror-B: D5/B/S3/Arith/DivisorGibbs/FullWindowDivisorBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fibonacci prime-power windows are nonzero and exhaust every positive divisor. -/

import D5.S3.Arith.DivisorGibbs.FiniteDivisorEulerProduct
import D5.S3.Arith.DivisorGibbs.CofinalDivisibility
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Arith.DivisorGibbs.FullWindowDivisorBridge

open scoped BigOperators
open FiniteDivisorEulerProduct

/-- The first `k` primes, each raised to the Fibonacci exponent `fib (k+2)-1`. -/
def M (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (Nat.nth Nat.Prime i) ^ (Nat.fib (k + 2) - 1)

/-- The finite Euler identity, cofinal divisibility, and extension by zero hold together
for the actual divisor polynomial and the specified Fibonacci prime-power windows. -/
theorem finite_divisor_bridge :
    (∀ (n : ℕ) (s : ℂ), 0 < n → Z n s = ∏ p ∈ n.primeFactors,
      ∑ j ∈ Finset.range (n.factorization p + 1), ((p : ℂ) ^ (-s)) ^ j) ∧
    ((∀ k, M k ≠ 0) ∧ (∀ d : ℕ, 0 < d → ∀ᶠ k in Filter.atTop, d ∣ M k)) ∧
    (∀ (k : ℕ) (s : ℂ),
      Z (M k) s = ∑' d : ℕ, if d ∈ (M k).divisors then (d : ℂ) ^ (-s) else 0) := by
  refine ⟨divisor_sum_eq_euler_product, ⟨?_, ?_⟩, ?_⟩
  · intro k
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      pow_ne_zero _ (Nat.prime_nth_prime i).ne_zero
  · intro d hd
    obtain ⟨hcutoff, _⟩ := CofinalDivisibility.cofinal_divisibility_ladder d hd
    exact Filter.eventually_atTop.mpr ⟨_, hcutoff⟩
  · intro k s
    exact divisor_sum_eq_tsum (M k) s

example : M 0 = 1 := by simp [M]
example : ℕ × ℂ := (0, 0)

#print axioms finite_divisor_bridge

end D5.S3.Arith.DivisorGibbs.FullWindowDivisorBridge
