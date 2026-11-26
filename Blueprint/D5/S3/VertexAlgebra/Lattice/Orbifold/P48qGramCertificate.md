# The P48q Gram Certificate

## Abstract

The integral Gram matrix in the P48q catalogue basis has an integral inverse and is preserved by the concrete order-three row action.

**Definition 1.1 (The catalogue Gram matrix).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.nebeGram`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.nebeGram` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

G is the symmetric integer matrix obtained from the triangular GRAM table in the Nebe–Sloane catalogue’s P48q entry, with both axes indexed by Fin 48.

**Definition 1.2 (The integral inverse table).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.nebeGramInverse`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.nebeGramInverse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

The inverse is an explicit integer matrix H in the same basis as G.

**Definition 1.3 (The rank-48 lattice data).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.nebeLatticeData`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.nebeLatticeData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

The rank-48 lattice data uses G as its integral form. The symmetry and evenness of each diagonal entry are checked directly on the table.

**Theorem 1.4 (The inverse product is the identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.gram_inverse_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.gram_inverse_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

The integral matrices satisfy HG = I. The rowwise integer dot products give HGᵀ = I, and the catalogue Gram matrix is symmetric.

**Theorem 1.5 (The order-three action preserves the form).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.gram_isometry_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.gram_isometry_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

M is the fourth power of the first catalogue generator, as in the P48q fixed-rank certificate. In the catalogue’s row coordinates the action is x ↦ xM, so preservation of the Gram form is MGMᵀ = G.

The first rowwise check multiplies M by G and verifies the intermediate table. The second multiplies that table by Mᵀ and recovers G. Both checks use exact integer dot products.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.gram_inverse_certificate`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.gram_isometry_certificate`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.nebeGram`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.nebeGramInverse`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate.nebeLatticeData`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate](P48qFixedRankCertificate.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality](../../LatticeGeneratingFieldLocality.md)
