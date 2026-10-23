# Original cosine determinant interface

## Abstract

The original six-cosh cosine numerator and determinant identity for one target edge.

For ordered local edge cosh coordinates (r,a,b,o,c,d), gram is the signed four-by-four Gram matrix. D1 and D2 are the two target-edge quadratic factors, and N is the original cosine numerator.

**Theorem 1.1 (Original cosine determinant interface).**

$$\left(\left(\left(\left(\left(1 < r \land 1 < a\right) \land 1 < b\right) \land 1 < o\right) \land 1 < c\right) \land 1 < d\right) \Rightarrow \left(\left(\left(0 < \operatorname{D1}\left(r, a, d\right) \land 0 < \operatorname{D2}\left(r, b, c\right)\right) \land \operatorname{D1}\left(r, a, d\right) \cdot \operatorname{D2}\left(r, b, c\right) - \operatorname{N}\left(r, a, b, o, c, d\right)^{2} = -\left(r^{2} - 1\right) \cdot \operatorname{det}\left(\operatorname{gram}\left(r, a, b, o, c, d\right)\right)\right) \land \left(\operatorname{det}\left(\operatorname{gram}\left(r, a, b, o, c, d\right)\right) < 0 \Leftrightarrow 0 < \operatorname{D1}\left(r, a, d\right) \cdot \operatorname{D2}\left(r, b, c\right) - \operatorname{N}\left(r, a, b, o, c, d\right)^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface.original_cosine_interface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem packages the positive target-edge factors, the exact determinant identity, and the resulting strict sign criterion in one algebraic interface.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface.original_cosine_interface`
