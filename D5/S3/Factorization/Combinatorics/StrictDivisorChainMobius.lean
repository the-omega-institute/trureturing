/- GID: D5/S3/Factorization/Combinatorics/StrictDivisorChainMobius
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/StrictDivisorChainMobius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The alternating number of strict divisor chains from one to a positive integer equals its Möbius value. -/

import D5.S3.Factorization.Combinatorics.StrictDivisorChainCount
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

set_option autoImplicit false

open scoped BigOperators
open D5.S3.Factorization.Combinatorics.StrictDivisorChainCount

namespace D5.S3.Factorization.Combinatorics.StrictDivisorChainMobius

/-- The alternating count of strict divisor chains, through the prime-factor rank of the endpoint. -/
noncomputable def chainSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (ArithmeticFunction.cardFactors n + 1),
    (-1 : ℤ) ^ k * (Nat.card (Chain n k) : ℤ)

/-- The alternating count of strict divisor chains to a positive integer is its Möbius value. -/
set_option maxHeartbeats 800000 in
 theorem chain_alternating_sum_eq_moebius (n : ℕ) (hn : 1 ≤ n) :
    chainSum n = ArithmeticFunction.moebius n := by
  classical
  sorry

end D5.S3.Factorization.Combinatorics.StrictDivisorChainMobius
