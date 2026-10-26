# Original cosine determinant interface

## Abstract

The original six-cosh cosine numerator and determinant identity for one target edge.

Application to all six original coordinates. Fix x=(r,a,b,o,c,d) in the edge order (12,13,14,34,24,23), with every coordinate greater than one. Put phi(r,a,b,o,c,d)=N(r,a,b,o,c,d)/(sqrt(D1(r,a,d))*sqrt(D2(r,b,c))). This is the same original cosine formula of FourCycleEnvelopes. The six target-edge argument lists are (r,a,b,o,c,d), (a,r,b,c,o,d), (b,r,a,d,o,c), (o,a,d,r,c,b), (c,r,d,a,o,b), and (d,r,c,b,o,a), in that edge order.

For each argument list, the corresponding vertex permutation sends its Gram matrix to a simultaneous row and column permutation of the same original G. Its determinant is therefore det(G), and both target radicands are positive. Applying original_cosine_interface and dividing by their product gives 1-phi_e^2=-(x_e^2-1)*det(G)/(D_e1*D_e2). Consequently det(G)<0 is equivalent to all six unchanged original cosines lying strictly between -1 and 1. These are finite algebraic and analytic statements on the supplied coordinates; a geometric realization and compatible global face gluing require their own interfaces.

For ordered local edge cosh coordinates (r,a,b,o,c,d), gram is the signed four-by-four Gram matrix. D1 and D2 are the two target-edge quadratic factors, and N is the original cosine numerator.

**Theorem 1.1 (Original cosine determinant interface).**

$$\left(\left(\left(\left(\left(1 < r \land 1 < a\right) \land 1 < b\right) \land 1 < o\right) \land 1 < c\right) \land 1 < d\right) \Rightarrow \left(\left(\left(0 < \operatorname{D1}\left(r, a, d\right) \land 0 < \operatorname{D2}\left(r, b, c\right)\right) \land \operatorname{D1}\left(r, a, d\right) \cdot \operatorname{D2}\left(r, b, c\right) - \operatorname{N}\left(r, a, b, o, c, d\right)^{2} = -\left(r^{2} - 1\right) \cdot \operatorname{det}\left(\operatorname{gram}\left(r, a, b, o, c, d\right)\right)\right) \land \left(\operatorname{det}\left(\operatorname{gram}\left(r, a, b, o, c, d\right)\right) < 0 \Leftrightarrow 0 < \operatorname{D1}\left(r, a, d\right) \cdot \operatorname{D2}\left(r, b, c\right) - \operatorname{N}\left(r, a, b, o, c, d\right)^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface.original_cosine_interface` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem packages the positive target-edge factors, the exact determinant identity, and the resulting strict sign criterion in one algebraic interface.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface.original_cosine_interface`
