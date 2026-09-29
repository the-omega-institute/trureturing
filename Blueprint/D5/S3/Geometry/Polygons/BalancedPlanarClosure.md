# Balanced planar closure

## Abstract

Actual closed planar configurations for arbitrary finite balanced nonnegative lengths.

**Theorem 1.1 (Balanced lengths admit a closed complex configuration).**

Lean statement: `D5/S3/Geometry/Polygons/BalancedPlanarClosure.result`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/BalancedPlanarClosure.result` (`✓ std3`). ∎

*Citation.* Jean-Claude Hausmann and Allen Knutson (1996). *Polygon spaces and Grassmannians*. DOI: [10.48550/arXiv.dg-ga/9602012](https://doi.org/10.48550/arXiv.dg-ga/9602012). URL: <https://arxiv.org/abs/dg-ga/9602012v1>.

*Commentary.*

For every natural m and L:Fin(m)->Real, if every L(i) is nonnegative and twice each L(i) is at most the total sum, there exist complex vectors v(i) with norm L(i) whose sum is zero. The empty family, zero lengths, and equality in the balance inequalities are included.

The proof constructs every nonnegative resultant r at most the total S for which 2*L(i)<=S+r. In the induction step adding t, choose the previous resultant s=min(S,r+t). The deficit inequalities ensure both old attainability and abs(s-t)<=r<=s+t. A continuous norm function on a connected complex circle attains all values between the opposed and aligned endpoints. A zero previous resultant is handled directly.

Hausmann and Knutson, Corollary (4.2), identify the attainable planar lengths of perimeter two with the closed hypersimplex. Their polygon spaces include zero edges and collinear boundary configurations. Positive total length reduces to that normalization by rescaling. The all-zero and empty families, excluded by that normalization, are realized directly by zero vectors here. The Library note records the precise source and scope bridge.

This independently formalizes the classical planar closure criterion and makes no mathematical novelty claim. It supplies the geometric existence step used in codimension-one phase support; it does not establish interpolation, binary homogeneous factorization, local product measurements, or recovery on all matrices with arbitrary references.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/BalancedPlanarClosure.result`
