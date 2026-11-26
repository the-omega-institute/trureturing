# Positive Definiteness of the P48q Gram Matrix

## Abstract

The concrete P48q catalogue Gram matrix is positive definite over the reals.

**Theorem 1.1 (The catalogue Gram matrix is positive definite).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.nebeGram_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.nebeGram_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

Let G be the rank-48 integer Gram matrix from P48qGramCertificate. Its existing lattice data supplies symmetry. The certificate gives an integral upper triangular matrix U with positive diagonal, and checks by exact rowwise integer dot products that GU is lower triangular with positive diagonal.

Symmetry and triangularity give UᵀGU = diag(Uᵢᵢ(GU)ᵢᵢ). The diagonal is strictly positive. After casting to real matrices, U is invertible because its triangular determinant is nonzero, so positive definiteness transfers by congruence to the original real Gram matrix.

This proves positivity of the actual form used in the P48q lattice data and supplies the positive form for the twisted construction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.nebeGram_posDef`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate](P48qGramCertificate.md)
