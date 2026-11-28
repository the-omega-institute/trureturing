# Rank-one transfer reflection bound

## Abstract

A matrix-valued reflection estimate for the normalized signed-transfer polynomial.

**Definition 1.1 (Polynomial evaluation).**

Lean statement: `D5/S3/HilbertOperators/WuTransferReflectionBound.transferEval`

*Formalization.* `D5/S3/HilbertOperators/WuTransferReflectionBound.transferEval` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The coefficient sequence is evaluated at a complex argument through the finite matrix polynomial sum from degree zero through N in a finite complex matrix algebra.

**Theorem 1.2 (First coefficient bound).**

Lean statement: `D5/S3/HilbertOperators/WuTransferReflectionBound.firstCoeff_le_of_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/WuTransferReflectionBound.firstCoeff_le_of_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let N be positive. Assume a normalized matrix polynomial has Hermitian coefficients, constant coefficient I, and reflection product equal to the scalar product of 1 − aᵢ²z² with nonnegative real parameters aᵢ, allowing repetitions and zeros. Then its linear coefficient is at most (sumᵢ aᵢ)I in the Loewner order.

The proof first bounds the normalized matrix function on the imaginary axis, extends the bound to the closed right half-plane by the maximum-modulus argument, and differentiates the real ray at zero. The complex matrix norm and C-star order are handled by the imported Mathlib analysis.

## References

- Truth anchor: `D5/S3/HilbertOperators/WuTransferReflectionBound.firstCoeff_le_of_reflection`
- Truth anchor: `D5/S3/HilbertOperators/WuTransferReflectionBound.transferEval`
