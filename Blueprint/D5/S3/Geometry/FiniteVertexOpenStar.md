# Based contractions of finite relative open vertex stars

## Abstract

Relative open stars contract through actual face coordinates.

**Definition 1.1 (The relative open star).**

Lean statement: `D5/S3/Geometry/FiniteVertexOpenStar.star`

*Formalization.* `D5/S3/Geometry/FiniteVertexOpenStar.star` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a pre-abstract simplicial complex M on a finite vertex type V, the star at v is the subspace of the actual coordinate realization on which coordinate v is strictly positive. No purity or link condition is assumed.

**Theorem 1.2 (The star is relatively open).**

Lean statement: `D5/S3/Geometry/FiniteVertexOpenStar.isOpen_star`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexOpenStar.isOpen_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate evaluation is continuous, so its inverse image of the strictly positive real half-line is open in the realization. This openness assertion does not require a Fintype instance.

**Theorem 1.3 (The realized vertex belongs to its star).**

Lean statement: `D5/S3/Geometry/FiniteVertexOpenStar.vertex_mem_star`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteVertexOpenStar.vertex_mem_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton face at v supplies the actual coordinate vertex, whose v coordinate is one. This assertion is used by the based contraction and the finite bouquet cover.

**Definition 1.4 (A contraction fixing the chosen vertex).**

Lean statement: `D5/S3/Geometry/FiniteVertexOpenStar.contraction`

*Formalization.* `D5/S3/Geometry/FiniteVertexOpenStar.contraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every singleton face at v, the actual star has a jointly continuous homotopy relative to that vertex from its identity map to the constant vertex map. At time t the vector is (1-t)x+t e_v. Positivity of x_v forces every face witnessing x to contain v, so convexity keeps the whole segment in the same face. Its v coordinate stays positive, including t=1. Finite-coordinate continuity and the displayed formula prove the fixed-vertex condition. The construction consumes FiniteVertexCylinder.vertexPoint and the existing face-simplex coordinate description.

## References

- Truth anchor: `D5/S3/Geometry/FiniteVertexOpenStar.contraction`
- Truth anchor: `D5/S3/Geometry/FiniteVertexOpenStar.isOpen_star`
- Truth anchor: `D5/S3/Geometry/FiniteVertexOpenStar.star`
- Truth anchor: `D5/S3/Geometry/FiniteVertexOpenStar.vertex_mem_star`
- Dependency: [D5/S3/Geometry/FiniteVertexCylinder](FiniteVertexCylinder.md)
