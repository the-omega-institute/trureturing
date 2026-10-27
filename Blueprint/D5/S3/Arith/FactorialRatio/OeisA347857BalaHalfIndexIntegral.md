# Bala A347857: integrality at every natural index

## Abstract

Bala A347857 integrality.

**Definition 1.1 (a).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(6 \cdot n\right): \mathbb{R})}{(\operatorname{Nat}.\operatorname{factorial}\left(3 \cdot n\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot n\right): \mathbb{R})} \cdot \frac{\operatorname{OeisA347854BalaHalfIndexIntegral}.\operatorname{ffact}\left(\frac{3 \cdot (n: \mathbb{R})}{2}\right)}{\operatorname{OeisA347854BalaHalfIndexIntegral}.\operatorname{ffact}\left(\frac{5 \cdot (n: \mathbb{R})}{2}\right)}$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.a` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347857, NAME (unpaginated): "a(n) = (6*n)!/((3*n)!*(2*n)!) * (3*n/2)!/(5*n/2)!." Natural factorials are cast to the reals; fractional factorials use ffact.

**Definition 1.2 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{R}) = \operatorname{a}\left(n\right))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.claim` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347857, COMMENTS (unpaginated): "The sequence is conjectured to be integral." Integrality means that for every natural index, including zero, the value is the cast of an integer.

**Theorem 1.3 (result).**

$$\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{R}) = \operatorname{a}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a347857-bala-half-index-integrality` (proved) by `D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a347857-bala-half-index-integrality","declaration_gid":"D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

Every natural index has an integer value. Reduction to factorial quotients and comparison of prime valuations give an integer cast.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.a`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347857BalaHalfIndexIntegral.result`
- Dependency: [D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral](OeisA347854BalaHalfIndexIntegral.md)
