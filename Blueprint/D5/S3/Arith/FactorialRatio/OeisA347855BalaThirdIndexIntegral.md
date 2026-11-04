# Bala A347855: integrality at every natural index

## Abstract

Bala A347855 integrality.

**Definition 1.1 (a).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(4 \cdot n\right): \mathbb{R})}{(\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot n\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n\right): \mathbb{R})} \cdot \frac{\operatorname{OeisA347854BalaHalfIndexIntegral}.\operatorname{ffact}\left(\frac{(n: \mathbb{R})}{3}\right)}{\operatorname{OeisA347854BalaHalfIndexIntegral}.\operatorname{ffact}\left(\frac{4 \cdot (n: \mathbb{R})}{3}\right)}$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.a` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347855, NAME (unpaginated): "a(n) = (4*n)!/((2*n)!*(n)!) * (n/3)!/(4*n/3)!." Natural factorials are cast to the reals; fractional factorials use ffact.

**Definition 1.2 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{R}) = \operatorname{a}\left(n\right))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.claim` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347855, COMMENTS (unpaginated): "The sequence is conjectured to be integral." Integrality means that for every natural index, including zero, the value is the cast of an integer.

**Definition 1.3 (progression).**

$$\forall n \in \mathbb{N},\; \operatorname{progression}\left(n\right) = \prod_{k \in \operatorname{Finset}.\operatorname{range}\left(n\right)} (n + 3 \cdot \left(k + 1\right))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.progression` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

The product of the n natural factors n+3(k+1), with k in Finset.range n.

**Theorem 1.4 (third_dvd).**

$$\forall n \in \mathbb{N},\; (\neg (3 \mid n)) \implies (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot n\right) \cdot \operatorname{Nat}.\operatorname{factorial}\left(n\right) \cdot \operatorname{progression}\left(n\right) \mid \operatorname{Nat}.\operatorname{factorial}\left(4 \cdot n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.third_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

When three does not divide n, the product of (2n)!, n! and progression n divides (4n)!. The prime three contributes no valuation to progression n; other primes are controlled by counts of divisible progression terms.

**Theorem 1.5 (result).**

$$\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{R}) = \operatorname{a}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a347855-bala-third-index-integrality` (proved) by `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a347855-bala-third-index-integrality","declaration_gid":"D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

Every natural index has an integer value. Reduction to factorial quotients and comparison of prime valuations give an integer cast.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.a`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.progression`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.result`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.third_dvd`
- Dependency: [D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral](OeisA347854BalaHalfIndexIntegral.md)
