# Bala A295462: binary spacing and oddness

## Abstract

Bala A295462 parity.

**Definition 1.1 (a).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \frac{(\operatorname{Nat}.\operatorname{factorial}\left(15 \cdot n\right): \mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(2 \cdot n\right): \mathbb{Q})}{(\operatorname{Nat}.\operatorname{factorial}\left(10 \cdot n\right): \mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(6 \cdot n\right): \mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(n\right): \mathbb{Q})}$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295462Parity.a` (`✓ std3`).

*Citation.* Peter Bala (2026). *OEIS A295462: binary-spacing parity conjecture*. URL: <https://oeis.org/A295462>.

*Commentary.*

OEIS A295462, NAME (unpaginated): "a(n) = (15*n)!*(2*n)!/((10*n)!*(6*n)!*n!)." Each natural factorial is cast to the rationals and division is exact.

**Definition 1.2 (spacedBits).**

$$\forall n \in \mathbb{N},\; \operatorname{spacedBits}\left(n\right) = (\forall i \in \mathbb{N},\; \forall j \in \mathbb{N},\; (i < j) \implies ((\operatorname{Nat}.\operatorname{testBit}\left(n, i\right) = \operatorname{true}) \implies ((\operatorname{Nat}.\operatorname{testBit}\left(n, j\right) = \operatorname{true}) \implies (i + 4 \le j))))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295462Parity.spacedBits` (`✓ std3`).

*Citation.* Peter Bala (2026). *OEIS A295462: binary-spacing parity conjecture*. URL: <https://oeis.org/A295462>.

*Commentary.*

OEIS A048718, COMMENTS (unpaginated): "Max. 1 one-bit occur in each range of four bits." Position i has weight 2^i. Every pair of occupied positions i < j has distance at least four; zero has empty support.

**Definition 1.3 (claim).**

$$\operatorname{claim} = (\forall n \in \mathbb{N},\; \exists m \in \mathbb{N},\; (\operatorname{a}\left(n\right) = (m: \mathbb{Q})) \land (\operatorname{Odd}\left(m\right) \iff \operatorname{spacedBits}\left(n\right)))$$

*Formalization.* `D5/S3/Arith/FactorialRatio/BalaA295462Parity.claim` (`✓ std3`).

*Citation.* Peter Bala (2026). *OEIS A295462: binary-spacing parity conjecture*. URL: <https://oeis.org/A295462>.

*Commentary.*

OEIS A295462, REFERENCES (%D, unpaginated): "Conjecture: a(n) is odd iff the 1 bits in the binary expansion of n are separated by at least three 0's, that is, iff n belongs to A048718." The index n ranges over all natural numbers, including zero; a natural m realizes the rational quotient and Odd tests m.

**Theorem 1.4 (result).**

$$\forall n \in \mathbb{N},\; \exists m \in \mathbb{N},\; (\operatorname{a}\left(n\right) = (m: \mathbb{Q})) \land (\operatorname{Odd}\left(m\right) \iff \operatorname{spacedBits}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/BalaA295462Parity.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala295462` (proved) by `D5/S3/Arith/FactorialRatio/BalaA295462Parity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala295462","declaration_gid":"D5/S3/Arith/FactorialRatio/BalaA295462Parity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala (2026). *OEIS A295462: binary-spacing parity conjecture*. URL: <https://oeis.org/A295462>.

*Commentary.*

Every quotient is a natural integer, and it is odd exactly when occupied binary positions are separated by at least four. The binary prime valuation is a sum of nonnegative floor defects. Spacing makes all defects zero. The first shorter gap forces one defect to equal one; a strict geometric bound controls the lower occupied positions.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295462Parity.a`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295462Parity.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295462Parity.result`
- Truth anchor: `D5/S3/Arith/FactorialRatio/BalaA295462Parity.spacedBits`
- Dependency: [D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral](OeisA347854BalaHalfIndexIntegral.md)
