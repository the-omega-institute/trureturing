# Closed Laws for the First Witt Rows

## Abstract

The first two closed Witt rows terminate or alternate with coefficients known in every degree.

**Theorem 1.1 (The pure factor and both coefficient rows are explicit).**

$$(1+X)\cdot(1-X)=1-X^{2},\\\forall k\in\mathbb{N}, \operatorname{coeff}(k, \operatorname{firstWittRow})=\operatorname{if}(k=0 \lor k=2, 1, 0),\\\forall k\in\mathbb{N}, \operatorname{coeff}(k, \operatorname{secondWittRow})=\operatorname{if}(k=1, 0, (-1)^{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/WittRowLaws.witt_row_closed_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pure-direction factorization cancels every odd contribution. For the a = 1 logarithmic row, only degrees zero and two have coefficient one. For the b = 1 row, the linear coefficient is zero and every other coefficient follows the alternating sign pattern in all degrees.

The proof reuses Mathlib's exact coefficient theorem for invOneSubPow and transports it through rescale at minus one. Formal power-series coefficient lemmas then identify the two closed rows; no second implementation of the geometric-series inverse is introduced.

## References

- Truth anchor: `D5/S1/Recurrence/Witt/WittRowLaws.witt_row_closed_laws`
