# A prime sigma-gcd is two or three

## Abstract

A prime sigma-gcd is two or three.

**Definition 1.1 (The exact OEIS conjecture).**

$$\forall k \in \mathbb{N},\; \operatorname{Prime}\left(k - 1\right) \Rightarrow \left(\operatorname{Prime}\left(k + 1\right) \Rightarrow \left(\operatorname{Prime}\left(\operatorname{gcd}\left(k, \operatorname{sigma}\left(1, k\right)\right)\right) \Rightarrow \left(\operatorname{gcd}\left(k, \operatorname{sigma}\left(1, k\right)\right) = 2 \lor \operatorname{gcd}\left(k, \operatorname{sigma}\left(1, k\right)\right) = 3\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second A394757 conjecture asserts that a prime gcd of a twin-prime center and its divisor sum equals two or three. The claim retains both neighboring-prime hypotheses and quantifies over every natural center.

**Theorem 1.2 (The universal implication).**

$$\forall k \in \mathbb{N},\; \operatorname{Prime}\left(k - 1\right) \Rightarrow \left(\operatorname{Prime}\left(k + 1\right) \Rightarrow \left(\operatorname{Prime}\left(\operatorname{gcd}\left(k, \operatorname{sigma}\left(1, k\right)\right)\right) \Rightarrow \left(\operatorname{gcd}\left(k, \operatorname{sigma}\left(1, k\right)\right) = 2 \lor \operatorname{gcd}\left(k, \operatorname{sigma}\left(1, k\right)\right) = 3\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a394757-sigma-gcd-two-or-three` (proved) by `D5/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a394757-sigma-gcd-two-or-three","declaration_gid":"D5/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

If the divisor sum is even, two divides the prime gcd, which is therefore two. If it is odd, the shared square exclusion gives k=2t^2. Decompose nonzero t as 2^b r with r odd. Then k=2^(2b+1) r^2 and coprime multiplicativity expresses its divisor sum using the geometric sum for 2^(2b+1). The existing geometric-sum formula gives 2^(2b+2)-1, which is divisible by three because 4^(b+1) is congruent to one modulo three. The existing three_center theorem also gives three dividing k, so the prime gcd equals three. This settles preregistration #15004; infinitude remains open.

## References

- Truth anchor: `D5/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree.claim`
- Truth anchor: `D5/S3/Arith/Robin/TwinPrimeSigmaGcdTwoOrThree.result`
- Dependency: [D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare](TwinPrimeSigmaGcdThreeTwiceSquare.md)
