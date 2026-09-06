# The Smallest Missing Prime

## Abstract

Missing-prime threshold tests reduce to the least prime not dividing the integer.

**Theorem 1.1 (Strict decrease across primes).**

$$\forall p \in \mathbb{N}, q \in \mathbb{N},\; \left(Prime\left(p\right) \land \left(Prime\left(q\right) \land p < q\right)\right) \Rightarrow goldenLayerMarginal\left(q, 1\right) < goldenLayerMarginal\left(p, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime.golden_layer_marginal_one_strictAnti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For primes p less than q, the first-layer marginal at q is strictly smaller than at p. Cancelling the first-layer ratio gives log(1 + 1/p) divided by log p. Its positive numerator strictly decreases with p and its positive denominator strictly increases. This comparison across primes is the new estimate used below; the existing decrease with layer number does not supply it.

**Theorem 1.2 (Threshold propagation).**

$$\forall p \in \mathbb{N}, q \in \mathbb{N}, lambda \in \mathbb{R},\; \left(Prime\left(p\right) \land \left(Prime\left(q\right) \land \left(q \le p \land goldenLayerMarginal\left(q, 1\right) \le lambda\right)\right)\right) \Rightarrow goldenLayerMarginal\left(p, 1\right) \le lambda$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime.golden_layer_marginal_one_threshold_of_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At any real price, a first-layer threshold valid at q is valid at every prime p at least q. Equality of primes is included. Consequently the implication also holds when both primes are required not to divide a given positive integer.

**Theorem 1.3 (The least missing prime decides the condition).**

$$\forall n \in \mathbb{N}, q \in \mathbb{N}, lambda \in \mathbb{R},\; IsLeast\left(\{p: \mathbb{N} \mid Prime\left(p\right) \land \neg{p \mid n}\}, q\right) \Rightarrow \left(\left(\forall p \in \mathbb{N},\; \left(Prime\left(p\right) \land \neg{p \mid n}\right) \Rightarrow goldenLayerMarginal\left(p, 1\right) \le lambda\right) \Leftrightarrow goldenLayerMarginal\left(q, 1\right) \le lambda\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime.golden_missing_prime_threshold_iff_of_isLeast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given the least prime q not dividing n, all missing primes have first-layer marginal at most the price exactly when q does. The reverse implication uses the new prime comparison. IsLeast includes both membership and minimality, so the hypothesis identifies an actual missing prime.

**Theorem 1.4 (Existence for every positive integer).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\exists q \in \mathbb{N},\; IsLeast\left(\{p: \mathbb{N} \mid Prime\left(p\right) \land \neg{p \mid n}\}, q\right) \land \left(\forall lambda \in \mathbb{R},\; \left(\forall p \in \mathbb{N},\; \left(Prime\left(p\right) \land \neg{p \mid n}\right) \Rightarrow goldenLayerMarginal\left(p, 1\right) \le lambda\right) \Leftrightarrow goldenLayerMarginal\left(q, 1\right) \le lambda\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime.exists_smallest_missing_prime_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer n at least one has a least missing prime q, and this single q decides the missing-prime condition for every real price. Mathlib supplies a prime above n, which cannot divide the positive integer n; Nat.find selects the least missing prime. The witness q is chosen before the price. No finite search bound or numerical threshold is assumed.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime.exists_smallest_missing_prime_threshold`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime.golden_layer_marginal_one_strictAnti`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime.golden_layer_marginal_one_threshold_of_le`
- Truth anchor: `D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime.golden_missing_prime_threshold_iff_of_isLeast`
- Dependency: [D5/S3/Arith/GoldenResourceOptimalInteger](../GoldenResourceOptimalInteger.md)
