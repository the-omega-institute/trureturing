# Hanna's A363569 Prime-Index Formula

## Abstract

Hanna's A363569 prime-index coefficient formula.

**Definition 1.1 (Hanna's A363569 conjecture).**

$$claim = (\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies ((3 < p) \implies (\operatorname{OeisA363569PowerOfTwo}.\operatorname{a}\left(p\right) = (p: \mathbb{C}) \cdot ((-1))^{\operatorname{Nat}.\operatorname{div}\left(p - 1, 2\right)} - 1)))$$

*Formalization.* `D5/S1/Recurrence/HannaBilateral/OeisA363569Prime.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

a(p) = p*(-1)^((p-1)/2) - 1 for primes p > 3 (conjecture). Source: OEIS A363569, FORMULA field (an unpaginated entry). Indices are natural numbers; values and numeric expressions on both sides are complex. Nat.div denotes natural-number division, so division by two is integer division.

**Theorem 1.2 (The A363569 prime-index formula).**

$$\forall p: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies ((3 < p) \implies (\operatorname{OeisA363569PowerOfTwo}.\operatorname{a}\left(p\right) = (p: \mathbb{C}) \cdot ((-1))^{\operatorname{Nat}.\operatorname{div}\left(p - 1, 2\right)} - 1))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/HannaBilateral/OeisA363569Prime.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

Apply the complex-parameter prime coefficient identity and simplify the indicated parameter powers.

## References

- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363569Prime.claim`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363569Prime.result`
- Dependency: [D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo](OeisA363558PowerOfTwo.md)
- Dependency: [D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo](OeisA363569PowerOfTwo.md)
