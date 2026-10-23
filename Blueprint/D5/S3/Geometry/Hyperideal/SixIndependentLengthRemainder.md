# The six-independent-length determinant remainder

## Abstract

Exact determinant remainder for the six-independent-length character coordinates.

The variables r, o, A, B, xi and zeta are real. The matrix gram is the four-by-four character-coordinate Gram matrix for the six independent length slice. The factors L and M are the two symmetric-center block determinants, while Xi is the exact quadratic-plus-quartic asymmetry remainder.

**Theorem 1.1 (Exact determinant remainder).**

$$\operatorname{det}\left(\operatorname{gram}\left(r, o, A, B, xi, zeta\right)\right) = - \operatorname{L}\left(r, o, A, B\right) \times \operatorname{M}\left(r, o, A, B\right) + \operatorname{Xi}\left(r, o, A, B, xi, zeta\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SixIndependentLengthRemainder.determinant_remainder_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the determinant in the character coordinates gives det(gram) = -L*M + Xi. This is an algebraic identity over the reals; it does not assert a global CFMP realization or a maximal stability ball.

**Theorem 1.2 (Strict determinant criterion).**

$$\operatorname{det}\left(\operatorname{gram}\left(r, o, A, B, xi, zeta\right)\right) < 0 \Leftrightarrow \operatorname{Xi}\left(r, o, A, B, xi, zeta\right) < \operatorname{L}\left(r, o, A, B\right) \cdot \operatorname{M}\left(r, o, A, B\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SixIndependentLengthRemainder.determinant_negative_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant is negative exactly when the asymmetry remainder is strictly smaller than the product L*M. The geometric interpretation still requires the separate positive-length and realization hypotheses of the surrounding theory.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SixIndependentLengthRemainder.determinant_negative_iff`
- Truth anchor: `D5/S3/Geometry/Hyperideal/SixIndependentLengthRemainder.determinant_remainder_identity`
