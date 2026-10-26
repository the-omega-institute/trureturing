# Bala A276102: integrality at every natural index

## Abstract

Bala A276102 integrality.

**Definition 1.1 (a).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(6 \cdot n\right): \mathbb{R}) \cdot \operatorname{Real}.\operatorname{Gamma}\left(\frac{(n: \mathbb{R})}{5} + 1\right)}{(\operatorname{Nat}.\operatorname{factorial}\left(3 \cdot n\right): \mathbb{R}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot n\right): \mathbb{R}) \cdot \operatorname{Real}.\operatorname{Gamma}\left(\frac{6 \cdot (n: \mathbb{R})}{5} + 1\right)}$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.a` (`✓ std3`).

*Citation.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

OEIS A276102, NAME (unpaginated): "a(n) = (6*n)!*(n/5)!/((3*n)!*(2*n)!*(6*n/5)!)." Bala, page 1: "throughout these notes x! is shorthand for Γ(x + 1)". Natural factorials are cast to the reals.

**Definition 1.2 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{a}\left(n\right) = (z: \mathbb{R}))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.claim` (`✓ std3`).

*Citation.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

OEIS A276102, COMMENTS (unpaginated): "This is only conjecturally an integer sequence." Bala, page 5: "are also integral for n ≥ 0." Naturals include zero, and integrality means equality to the real cast of an integer.

**Theorem 1.3 (result).**

$$\forall n \in \mathbb{N},\; \exists z \in \mathbb{Z},\; \operatorname{a}\left(n\right) = (z: \mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.result` (`✓ std3`). ∎

*Resolves.* `Problems/bfrac-fracfactorial` (proved) by `D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bfrac-fracfactorial","declaration_gid":"D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2016). *Some integer ratios of factorials*. URL: <https://oeis.org/A276098/a276098.pdf>.

*Commentary.*

Every natural index gives the real cast of an integer. Gamma recurrence and prime valuations prove the assertion for fifth indices, including zero.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.a`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/OeisA276102BalaFifthIndexIntegral.result`
- Dependency: [D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral](OeisA276101BalaThirdIndexIntegral.md)
