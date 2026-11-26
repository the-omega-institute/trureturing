# The P48q Order-Three Fixed-Rank Certificate

## Abstract

An exact integer matrix from the P48q lattice catalogue has cube one and both nonconstant traces zero. Its fixed space has dimension sixteen over every characteristic-zero field.

**Definition 1.1 (The integer row-action matrix).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

M is the fourth power of the first generator in the Nebe–Sloane catalogue’s P48q entry. The exact entries form a matrix indexed by Fin 48 on both axes. The catalogue basis uses the row action x ↦ xM.

**Definition 1.2 (The column-coordinate linear map).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.rowAction`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.rowAction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

For a field K and an integer matrix A indexed by Fin 48 on both axes, transpose A, cast each entry to K, and use left matrix multiplication to act on K^48. This realizes the row-coordinate action x ↦ xA on column coordinates.

**Theorem 1.3 (The cube is the identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_cube`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

The integer matrix M satisfies M³ = I. A rowwise dot-product check proves that the square table is M². A second check multiplies that square by M and gives each row of the identity. List sums agree with the matrix multiplication sums.

**Theorem 1.4 (The trace of the matrix is zero).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_trace`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

The diagonal entries of M sum to zero over the integers.

**Theorem 1.5 (The trace of its square is zero).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_trace_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_trace_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

The diagonal entries of the verified square M² sum to zero over the integers.

**Theorem 1.6 (The fixed space has dimension sixteen).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_fixedRank16`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_fixedRank16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

For every characteristic-zero field K, write T for the linear map on K^48 with matrix Mᵀ after casting the entries to K. Then ker(T − I) has dimension sixteen over K.

Transposition and the integer cast preserve the cube relation and the two traces. The powers I, T and T² define a representation of the cyclic group of order three whose invariant space is ker(T − I). The character average gives dimension (48 + 0 + 0)/3 = 16, in agreement with the fixed dimension in Table 2 of Nebe’s paper.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_cube`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_fixedRank16`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_trace`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.nebeOrderThree_trace_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.rowAction`
