# Positive Definiteness of the P48q Gram Matrix

## Abstract

An exact triangular certificate proves positive definiteness of a symmetric integer matrix over the reals. The P48q catalogue Gram matrix satisfies the criterion.

**Theorem 1.1 (Soundness of the integer triangular certificate).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.posDef_intCast_of_triangular`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.posDef_intCast_of_triangular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G and U be integer matrices indexed by any finite linearly ordered type. Suppose G is symmetric, U is upper triangular, GU is lower triangular, and the diagonals of U and GU are strictly positive.

The matrix UᵀGU is lower triangular and symmetric, so it is diagonal. Only the diagonal summand contributes to its i-th diagonal entry, which is Uᵢᵢ(GU)ᵢᵢ > 0. Over the reals, U is invertible because its triangular determinant is nonzero. Mathlib's diagonal positivity and invertible congruence lemmas then give positive definiteness of the real cast of G.

**Theorem 1.2 (The catalogue Gram matrix is positive definite).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.nebeGram_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.nebeGram_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

The rank-48 integer Gram matrix G comes from P48qGramCertificate, whose lattice data supplies symmetry. The stored columns give an integer upper triangular matrix U with positive diagonal. Exact rowwise integer dot products establish that GU is lower triangular with positive diagonal. Applying the triangular criterion proves positive definiteness of the real form used in the P48q lattice data.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.nebeGram_posDef`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.posDef_intCast_of_triangular`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate](P48qGramCertificate.md)
