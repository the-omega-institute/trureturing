# Bala A347855: integrality at every natural index

## Abstract

Bala A347855 integrality.

**Definition 1.1 (b).**

$$\forall n \in \mathbb{N},\; \operatorname{b}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(12 \cdot n + 4\right): \mathbb{Q})}{(\operatorname{Nat}.\operatorname{factorial}\left(6 \cdot n + 2\right): \mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(3 \cdot n + 1\right): \mathbb{Q}) \cdot \prod_{k \in \operatorname{Finset}.\operatorname{range}\left(3 \cdot n + 1\right)} ((3 \cdot n + 3 \cdot k + 4: \mathbb{Q}))}$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxBIntegral.b` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347855, FORMULA (unpaginated): "a(3*n+1) = 3^(3*n+1) * b(n), where b(n) = (12*n+4)!/( (6*n+2)!*(3*n+1)!*Product_{k = 0..3*n} (3*n+3*k+4) ) appears to be integral." The product includes both endpoints given by the source; Finset.range uses an exclusive upper endpoint.

**Definition 1.2 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \operatorname{b}\left(n\right))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxBIntegral.claim` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347855, FORMULA (unpaginated): "a(3*n+1) = 3^(3*n+1) * b(n), where b(n) = (12*n+4)!/( (6*n+2)!*(3*n+1)!*Product_{k = 0..3*n} (3*n+3*k+4) ) appears to be integral." Integrality means that for every natural index, including zero, the value is the cast of an integer.

**Theorem 1.3 (result).**

$$\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \operatorname{b}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxBIntegral.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a347855-bala-aux-b-integrality` (proved) by `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxBIntegral.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a347855-bala-aux-b-integrality","declaration_gid":"D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxBIntegral.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

Every natural index has an integer value. The Gamma recurrence and the divisible factorial denominator give an integer cast.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxBIntegral.b`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxBIntegral.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxBIntegral.result`
- Dependency: [D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral](OeisA347855BalaThirdIndexIntegral.md)
