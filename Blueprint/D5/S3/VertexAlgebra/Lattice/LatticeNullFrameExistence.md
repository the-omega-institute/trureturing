# LatticeNullFrameExistence

## Abstract

Original lattice light-cone algebra

The actual inverse-Gram equation and complex algebraic closure give charge-dependent light-cone frames. The transverse dimension and basis are derived from the explicit frame equivalence, without a supplied splitting certificate. This is complex bilinear algebra on the original carrier, not an integral lattice isometry or a positive-form assertion.

**Theorem 1.1 (gramBilin_nondegenerate).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.gramBilin_nondegenerate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.gramBilin_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original even integral symmetric D and complex matrix H with H * gramComplex D = 1, the actual complex Gram bilinear form is nondegenerate. This is derived from determinants of the inverse equation, not assumed from rank.

**Theorem 1.2 (exists_nullFrame_pPlus_ne_zero).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.exists_nullFrame_pPlus_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.exists_nullFrame_pPlus_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D, complex H with H * gramComplex D = 1, rank at least two, and nonzero original integral p:Charge D, there exists an actual NullFrame D with pPlus(p) nonzero. A Mathlib orthogonal basis and a complex square root construct a null vector detected by p, then a genuinely paired vector is normalized and its self-pairing removed. The frame may depend on p. Zero charge is excluded; no uniform frame or positivity is asserted.

**Theorem 1.3 (Exact transverse dimension).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.finrank_K_add_two`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.finrank_K_add_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original D and every actual NullFrame F, finrank of its actual simultaneous Gram-orthogonal complement plus two equals D.rank. This is derived from the explicit frameEquiv and finite-dimensional product arithmetic; it has no inverse-Gram premise and assumes no basis or complement certificate.

**Definition 1.4 (Basis of the actual transverse subspace).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.transverseBasis`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.transverseBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original D and actual F, the chosen finite-dimensional basis of the actual F.K is reindexed by the proved dimension equality to Fin(D.rank-2). At rank 26 this gives an actual Fin 24 basis. It does not orthogonalize or replace the integral charge lattice.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.exists_nullFrame_pPlus_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.finrank_K_add_two`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.gramBilin_nondegenerate`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence.transverseBasis`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates](LatticeLightConeCoordinates.md)
