# Hanna's A363569 Power-of-Two Formula

## Abstract

Hanna's A363569 power-of-two coefficient formula.

**Definition 1.1 (The A363569 sequence).**

$$\forall m: \mathbb{N}, \operatorname{a}\left(m\right) = \operatorname{OeisA363558PowerOfTwo}.\operatorname{coeffA}\left(\operatorname{Complex}.\operatorname{I}, m\right)$$

*Formalization.* `D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo.a` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

Expansion of g.f. A(x) = Sum_{n=-oo..+oo} x^n * (i + x^n)^(2*n), where i^2 = -1. The parameter is Complex.I.

**Definition 1.2 (Hanna's A363569 conjecture).**

$$claim = (\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left((2)^{n}\right) = 1))$$

*Formalization.* `D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

a(2^n) = 1 for n > 0 (conjecture). Source: OEIS A363569, FORMULA field (an unpaginated entry). Indices are natural numbers; values and numeric expressions on both sides are complex. The displayed hypotheses retain the source range.

**Theorem 1.3 (The A363569 power-of-two formula).**

$$\forall n: \mathbb{N}, (0 < n) \implies (\operatorname{a}\left((2)^{n}\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A363558, A363559, A363561 and A363569: bilateral power sums*. URL: <https://oeis.org/A363558>.

*Commentary.*

Apply the complex-parameter dyadic coefficient identity and simplify the indicated parameter powers.

## References

- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo.a`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo.claim`
- Truth anchor: `D5/S1/Recurrence/HannaBilateral/OeisA363569PowerOfTwo.result`
- Dependency: [D5/S1/Recurrence/HannaBilateral/OeisA363558PowerOfTwo](OeisA363558PowerOfTwo.md)
