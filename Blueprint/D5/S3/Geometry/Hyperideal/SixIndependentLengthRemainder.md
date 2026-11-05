# The six-independent-length determinant remainder

## Abstract

Exact determinant remainder for the six-independent-length character coordinates.

Application to the original Gram matrix. In the original edge order (12,13,14,34,24,23), write the six independent coordinates as (r,a,b,o,c,d), and set A=(a+c)/2, B=(b+d)/2, xi=(a-c)/2, zeta=(b-d)/2. Let U have columns (e0+e1)/sqrt(2), (e2+e3)/sqrt(2), (e0-e1)/sqrt(2), and (e2-e3)/sqrt(2). Both U-transpose*U and U*U-transpose are identity, and U-transpose*G*U is precisely gram(r,o,A,B,xi,zeta). Thus determinant_remainder_identity applies to the original G with these actual halfsum and halfdifference coordinates.

At xi=zeta=0, the first and last two coordinate blocks have determinants -L and M, and both cross blocks vanish. For the V4 center r=o, the orthogonal matrix with columns (1,1,1,1)/2, (1,1,-1,-1)/2, (1,-1,1,-1)/2, and (1,-1,-1,1)/2 diagonalizes the original G(r,A,B,r,A,B), in this order, with eigenvalues 1-r-A-B, 1-r+A+B, 1+r-A+B, and 1+r+A-B. The original determinant and the character determinant therefore retain the same sign; the basis change does not impose pairing symmetry on the six independent input coordinates.

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
