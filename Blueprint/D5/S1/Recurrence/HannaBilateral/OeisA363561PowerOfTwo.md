# Hanna's A363561 Power-of-Two Formula

## Abstract

Hanna's A363561 power-of-two coefficient formula.

**Definition 1.1 (The A363561 sequence).**

$$\forall m: \mathbb{N}, \operatorname{a}\left(m\right) = \operatorname{OeisA363558PowerOfTwo}.\operatorname{coeffA}\left((\operatorname{Real}.\operatorname{sqrt}\left(2\right): \mathbb{C}), m\right)$$

*Formalization.* `D5/S1/Recurrence/HannaBilateral/OeisA363561PowerOfTwo.a` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

G.f.: Sum_{n=-oo..+oo} x^n * (sqrt(2) + x^n)^(2*n). The parameter is the nonnegative real square root of 2, embedded in the complex numbers.

**Definition 1.2 (Hanna's A363561 conjecture).**

$$claim = (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left((2)^{n}\right) = (2)^{(2)^{n}}))$$

*Formalization.* `D5/S1/Recurrence/HannaBilateral/OeisA363561PowerOfTwo.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

a(2^n) = 2^(2^n) for n > 0 (conjecture). Source: OEIS A363561, FORMULA field (an unpaginated entry). Indices are natural numbers; values and numeric expressions on both sides are complex. The displayed hypotheses retain the source range.

**Theorem 1.3 (The A363561 power-of-two formula).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left((2)^{n}\right) = (2)^{(2)^{n}})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/HannaBilateral/OeisA363561PowerOfTwo.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

Apply the complex-parameter dyadic coefficient identity and simplify the indicated parameter powers.

## References

- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363561PowerOfTwo.a`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363561PowerOfTwo.claim`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363561PowerOfTwo.result`
- Dependency: [D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo](OeisA363558PowerOfTwo.md)
