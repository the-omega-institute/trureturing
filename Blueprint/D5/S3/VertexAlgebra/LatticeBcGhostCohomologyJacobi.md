# Finite coefficient sums

## Abstract

Full signed coefficient Jacobi on the original BRST quotient.

Every operation is the bilinear quotient product constructed from the actual tensor Y and unchanged original Q. The previously proved unrestricted tensor Borcherds theorem is reused, not recredited as a new proof.

**Theorem 1.1 (Finite left coefficient support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.leftTerm_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.leftTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite support survives passage from actual cycle products to quotient products.

**Theorem 1.2 (Finite signed right coefficient support).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.rightTerm_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.rightTerm_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete signed right coefficient sums are finite at every integer parameter.

**Theorem 1.3 (All integer homogeneous signed Jacobi).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A quotient class fixed by a parity projection is represented by applying that actual projection to any closed representative. The prior odd-Q proof ensures this projected representative remains closed; no unsupported homogeneous-representative assumption is made.

**Theorem 1.4 (Explicit four-component mixed identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.mixed_borcherds`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.mixed_borcherds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient identity includes all four even/odd components, with the actual Koszul signs and all integer mode parameters. Projection, finite sums, and quotient maps are linked by proved equalities.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.leftTerm_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.mixed_borcherds`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostCohomologyJacobi.rightTerm_finite`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostCohomologyModes](LatticeBcGhostCohomologyModes.md)
