# Bala A347858: integrality at every natural index

## Abstract

Bala A347858 integrality.

**Definition 1.1 (a).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(9 \cdot n\right): \mathbb{R})}{(\operatorname{Nat}.\operatorname{factorial}\left(3 \cdot n\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot n\right): \mathbb{R})} \cdot \frac{\operatorname{OeisA347854BalaHalfIndexIntegral}.\operatorname{ffact}\left(\frac{(n: \mathbb{R})}{2}\right)}{\operatorname{OeisA347854BalaHalfIndexIntegral}.\operatorname{ffact}\left(\frac{9 \cdot (n: \mathbb{R})}{2}\right)}$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347858BalaHalfIndexIntegral.a` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347858, NAME (unpaginated): "a(n) = (9*n)!/((3*n)!*(2*n)!) * (n/2)!/(9*n/2)!." Natural factorials are cast to the reals; fractional factorials use ffact.

**Definition 1.2 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{R}) = \operatorname{a}\left(n\right))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347858BalaHalfIndexIntegral.claim` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347858, COMMENTS (unpaginated): "The sequence is conjectured to be integral." Integrality means that for every natural index, including zero, the value is the cast of an integer.

**Theorem 1.3 (result).**

$$\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{R}) = \operatorname{a}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347858BalaHalfIndexIntegral.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a347858-bala-half-index-integrality` (proved) by `D5/S3/Arith/FactorialRatio/OeisA347858BalaHalfIndexIntegral.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a347858-bala-half-index-integrality","declaration_gid":"D5/S3/Arith/FactorialRatio/OeisA347858BalaHalfIndexIntegral.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

Every natural index has an integer value. Reduction to factorial quotients and comparison of prime valuations give an integer cast.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347858BalaHalfIndexIntegral.a`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347858BalaHalfIndexIntegral.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347858BalaHalfIndexIntegral.result`
- Dependency: [D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral](OeisA347854BalaHalfIndexIntegral.md)
