# The auxiliary scalar polynomial

## Abstract

Actual face counts are scalar coefficients with two low-degree corrections.

This is a repository-derived coefficient reorganization of source Theorem 3.6, with no novelty claim for the published face count.

**Theorem 1.1 (Geometric coefficients and the scalar sum).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeScalar.crownGeometricFaceCount_eq_scalar_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeScalar.crownGeometricFaceCount_eq_scalar_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For every positive n and natural d, the rational image of the actual geometric face count equals the coefficient of degree d in S_n, with two added when d is zero and one added when d is one. Here S_n is the sum, for 1 <= m <= n, of A(n,m)(1+X)^(n+m), where A(n,m)=(n/m)choose(n+m-1,2m-1). The proof discharges natural division, binomial support and the interchange of sums. S_n is an auxiliary polynomial, not the full geometric f-polynomial.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeScalar.crownGeometricFaceCount_eq_scalar_coeff`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopePositive](CrownOrderPolytopePositive.md)
