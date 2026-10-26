# LatticeSectorRankZero

## Abstract

Rank zero sector fields

**Definition 1.1 (rankZeroCoordinates).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorRankZero.rankZeroCoordinates`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorRankZero.rankZeroCoordinates` (`✓ std3`).

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

With no oscillator variables the oscillator algebra is canonically the complex scalar algebra. This coordinate map is consumed by the exact rank-zero field calculation.

**Theorem 1.2 (rankZero_field).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorRankZero.rankZero_field`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeSectorRankZero.rankZero_field` (`✓ std3`). ∎

*Citation.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Every charge is zero. The actual mixed field in scalar coordinates is scalar multiplication in mode minus one and zero in every other mode. The general classification and category-level universal equivalence retain this rank and give a one-dimensional IO space.

Classical free-boson conventions follow Bakalov-Kac and Matsuo-Nagatomo. This is the scalar boundary of the neutral sector theory, with no full charged lattice module, braiding, associator or CFT assertion.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorRankZero.rankZeroCoordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorRankZero.rankZero_field`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorMultiplicityFusion](LatticeSectorMultiplicityFusion.md)
