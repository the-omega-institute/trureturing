# Local Positive-Square Completion

## Abstract

An observer outside a finite real spectrum gives a positive inverse-square determinant completion.

**Definition 1.1 (Shifted inverse-square eigenvalue).**

Lean statement: `D5/S3/SpectralTopology/LocalPositiveSquareCompletion.shiftedInverseSquareEigenvalue`

*Formalization.* `D5/S3/SpectralTopology/LocalPositiveSquareCompletion.shiftedInverseSquareEigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight at spectral value h(j) is the reciprocal of the square of h(j) minus the observer coordinate.

**Definition 1.2 (Local positive square).**

Lean statement: `D5/S3/SpectralTopology/LocalPositiveSquareCompletion.localPositiveSquare`

*Formalization.* `D5/S3/SpectralTopology/LocalPositiveSquareCompletion.localPositiveSquare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local completion is the diagonal complex matrix formed from the shifted inverse-square weights.

**Theorem 1.3 (Off-spectrum shifts give positive determinant completions).**

$$\forall r\in \mathbb{N}, h: Fin\left(r\right) \to \mathbb{R}, a\in \mathbb{R}, \\{}{\forall j\in Fin\left(r\right), h\left(j\right) \neq a} \Rightarrow \\{}{{\forall j\in Fin\left(r\right), 0 < lambda\left(j\right)} \land PosDef\left(A\right) \land {\forall w\in \mathbb{C}, det\left(1 + w \cdot A\right) = \prod_{j\in Fin\left(r\right)} {1 + w \cdot lambda\left(j\right)}} \land {\forall w\in \mathbb{C}, det\left(1 + w \cdot A\right) = 0 \Rightarrow {Im\left(w\right) = 0 \land Re\left(w\right) < 0}}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/LocalPositiveSquareCompletion.local_positive_square_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h list the finite real spectrum and let a avoid every spectral value. Each difference h(j)-a is nonzero, so its squared reciprocal is strictly positive. The diagonal matrix A formed from these weights is therefore positive definite.

Mathlib's diagonal determinant identity gives the displayed factorization of det(I+wA). If the determinant vanishes, one positive factor weight forces w to be its negative reciprocal; hence every zero is real and strictly negative.

The off-spectrum premise is essential. The companion collision theorem records that Lean's total inverse sends a zero spectral difference to zero rather than to a positive weight.

**Theorem 1.4 (A spectral collision collapses the inverse-square weight).**

$$\forall a\in \mathbb{R}, lambda\left(a, a\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/LocalPositiveSquareCompletion.spectral_collision_collapses_inverse_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a one-point spectrum equal to the observer coordinate, the shifted difference is zero and the totalized real inverse-square weight is exactly zero. This is the concrete degeneracy excluded by the main theorem.

## References

- Truth anchor: `D5/S3/SpectralTopology/LocalPositiveSquareCompletion.localPositiveSquare`
- Truth anchor: `D5/S3/SpectralTopology/LocalPositiveSquareCompletion.local_positive_square_completion`
- Truth anchor: `D5/S3/SpectralTopology/LocalPositiveSquareCompletion.shiftedInverseSquareEigenvalue`
- Truth anchor: `D5/S3/SpectralTopology/LocalPositiveSquareCompletion.spectral_collision_collapses_inverse_square`
