# Hanna's A363559 Prime-Index Formula

## Abstract

Hanna's A363559 prime-index coefficient formula.

**Definition 1.1 (Hanna's A363559 conjecture).**

$$claim = (\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies ((3 < p) \implies (\operatorname{OeisA363559PowerOfTwo}.\operatorname{a}\left(p\right) = (p: \mathbb{C}) \cdot (3)^{p - 1} + (9)^{p})))$$

*Formalization.* `D5/S1/Recurrence/HannaBilateral/OeisA363559Prime.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

a(p) = p*3^(p-1) + 9^p for primes p > 3 (conjecture). Source: OEIS A363559, FORMULA field (an unpaginated entry). Indices are natural numbers; values and numeric expressions on both sides are complex. The displayed hypotheses retain the source range.

**Theorem 1.2 (The A363559 prime-index formula).**

$$\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies ((3 < p) \implies (\operatorname{OeisA363559PowerOfTwo}.\operatorname{a}\left(p\right) = (p: \mathbb{C}) \cdot (3)^{p - 1} + (9)^{p}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/HannaBilateral/OeisA363559Prime.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

Apply the complex-parameter prime coefficient identity and simplify the indicated parameter powers.

## References

- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363559Prime.claim`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363559Prime.result`
- Dependency: [D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo](OeisA363558PowerOfTwo.md)
- Dependency: [D5/S1/Recurrence/HannaBilateral/OeisA363559PowerOfTwo](OeisA363559PowerOfTwo.md)
