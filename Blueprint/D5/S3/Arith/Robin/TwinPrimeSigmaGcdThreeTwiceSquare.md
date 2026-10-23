# A sigma-gcd of three forces twice a square

## Abstract

A sigma-gcd of three forces twice a square.

**Theorem 1.1 (The square alternative is excluded above four).**

$$\forall k \in \mathbb{N},\; 4 < k \Rightarrow \left(\operatorname{Prime}\left(k - 1\right) \Rightarrow \left(\operatorname{Odd}\left(\operatorname{sigma}\left(1, k\right)\right) \Rightarrow \left(\exists m \in \mathbb{N},\; k = 2 \cdot m^{2}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.twice_square_of_odd_sigma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k greater than four, primality of k-1 excludes a square center. An odd divisor sum therefore forces k to be twice a square. The two-or-three theorem consumes this public helper.

**Definition 1.2 (The exact OEIS conjecture).**

$$\forall k \in \mathbb{N},\; \operatorname{Prime}\left(k - 1\right) \Rightarrow \left(\operatorname{Prime}\left(k + 1\right) \Rightarrow \left(\operatorname{gcd}\left(k, \operatorname{sigma}\left(1, k\right)\right) = 3 \Rightarrow \left(\exists m \in \mathbb{N},\; k = 2 \cdot m^{2}\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact A394399 conjecture asserts that every twin-prime center with sigma-gcd three is twice a square. The implication holds for all natural numbers with truncated natural subtraction.

**Theorem 1.3 (The universal implication).**

$$\forall k \in \mathbb{N},\; \operatorname{Prime}\left(k - 1\right) \Rightarrow \left(\operatorname{Prime}\left(k + 1\right) \Rightarrow \left(\operatorname{gcd}\left(k, \operatorname{sigma}\left(1, k\right)\right) = 3 \Rightarrow \left(\exists m \in \mathbb{N},\; k = 2 \cdot m^{2}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a394399-twin-prime-sigma-gcd-three` (proved) by `D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a394399-twin-prime-sigma-gcd-three","declaration_gid":"D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The existing even_center theorem forces two to divide the center. A gcd of three prevents two from dividing its divisor sum, so the sum is odd. The reused square-or-twice-square parity criterion supplies two alternatives. A square center factors k-1 as (s-1)(s+1); primality forces the boundary k=4, where sigma(4)=7 and the gcd is one. The remaining alternative is twice a square. This settles preregistration #15003; it proves no infinitude assertion.

## References

- Truth anchor: `D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.claim`
- Truth anchor: `D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.result`
- Truth anchor: `D5/S3/Arith/Robin/TwinPrimeSigmaGcdThreeTwiceSquare.twice_square_of_odd_sigma`
- Dependency: [D5/S3/Arith/KrizekTriangularSquareSigmaParity](../KrizekTriangularSquareSigmaParity.md)
- Dependency: [D5/S3/Factorization/TwinPrimeSigmaGcdDivisibility](../../Factorization/TwinPrimeSigmaGcdDivisibility.md)
