# Lagneau's Alternating Divisor-Sum Conjecture

## Abstract

A prime alternating sum of decreasing divisors above three forces a square or twice a square.

**Definition 1.1 (The alternating divisor sum).**

$$T\left(n\right) = alternatingSum\left(map\left(sort\left(divisors\left(n\right), (\mathord{\cdot} \ge \mathord{\cdot})\right), (\lambda d \in \mathbb{N} \mapsto (d : \mathbb{Z}))\right)\right)$$

*Formalization.* `D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare.T` (`✓ std3`).

*Citation.* Michel Lagneau (2012). *OEIS A193351, Numbers k such that A071324(k) is prime*. URL: <https://oeis.org/A193351>.

*Commentary.*

For each natural number n, T(n) is the integer alternating sum of its divisors nonincreasing, starting with n. Each divisor is coerced to an integer before the alternating sum is taken.

**Theorem 1.2 (Lagneau's A193351 conjecture).**

$$\forall n \in \mathbb{N},\; (3 < n) \Rightarrow ((Prime\left(toNat\left(T\left(n\right)\right)\right)) \Rightarrow ((\exists t \in \mathbb{N},\; n = t^{2}) \lor (\exists t \in \mathbb{N},\; n = 2 \cdot t^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare.lagneau_a193351` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a193351-alternating-divisor-sum-prime-square` (proved) by `D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare.lagneau_a193351`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a193351-alternating-divisor-sum-prime-square","declaration_gid":"D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare.lagneau_a193351","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Pairing the decreasing divisors gives T(n) at least n/2. For n greater than three, a prime T(n) is therefore not two and hence is odd. Alternating signs disappear modulo two, so T(n) has the parity of sigma(n). The classical characterization of odd sigma values then gives that n is a square or twice a square.

## References

- Truth anchor: `D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare.T`
- Truth anchor: `D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare.lagneau_a193351`
