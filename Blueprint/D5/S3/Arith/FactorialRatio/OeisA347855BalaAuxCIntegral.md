# Bala A347855: integrality at every natural index

## Abstract

Bala A347855 integrality.

**Definition 1.1 (c).**

$$\forall n \in \mathbb{N},\; \operatorname{c}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(12 \cdot n + 8\right): \mathbb{Q})}{(\operatorname{Nat}.\operatorname{factorial}\left(6 \cdot n + 4\right): \mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(3 \cdot n + 1\right): \mathbb{Q}) \cdot \prod_{k \in \operatorname{Finset}.\operatorname{range}\left(3 \cdot n + 3\right)} ((3 \cdot n + 3 \cdot k + 2: \mathbb{Q}))}$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral.c` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347855, FORMULA (unpaginated): "a(3*n+2) = 3^(3*n+2) * c(n), where c(n) = (12*n+8)!/( (6*n+4)!*(3*n+1)!*Product_{k = 0..3*n+2} (3*n+3*k+2) ) appears to be integral. (End)" The product includes both endpoints given by the source; Finset.range uses an exclusive upper endpoint.

**Definition 1.2 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \operatorname{c}\left(n\right))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral.claim` (`✓ std3`).

*Citation.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

OEIS A347855, FORMULA (unpaginated): "a(3*n+2) = 3^(3*n+2) * c(n), where c(n) = (12*n+8)!/( (6*n+4)!*(3*n+1)!*Product_{k = 0..3*n+2} (3*n+3*k+2) ) appears to be integral. (End)" Integrality means that for every natural index, including zero, the value is the cast of an integer.

**Theorem 1.3 (result).**

$$\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; (z: \mathbb{Q}) = \operatorname{c}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a347855-bala-aux-c-integrality` (proved) by `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a347855-bala-aux-c-integrality","declaration_gid":"D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2021). *OEIS A347854–A347858: fractional factorial ratios*. URL: <https://oeis.org/A347854>.

*Commentary.*

Every natural index has an integer value. The Gamma recurrence and the divisible factorial denominator give an integer cast.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral.c`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA347855BalaAuxCIntegral.result`
- Dependency: [D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral](OeisA347855BalaThirdIndexIntegral.md)
