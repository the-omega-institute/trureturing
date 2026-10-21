# Ground-first native right-current transport

## Abstract

Ground-first native right-current transport on the distinct source and actual tensor carriers.

The module retains both projected charged ground components, the source zero mode, signed physical lifts and the actual tensor current. It proves the simple-pole Ward collapse and a finite ordered eight-composition cancellation on the original tensor carrier.

**Theorem 1.1 (Positive source currents vanish on both projected ground components).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.projectedGround_positive_neutral`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.projectedGround_positive_neutral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two Bool-named projected signs are retained; every positive source neutral mode vanishes by the literal polynomial derivative formula.

**Theorem 1.2 (Ground Ward collapse).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.projectedGround_current_ward`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.projectedGround_current_ward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native Ward sum collapses to the source zero-mode output slice with its signed lift increment.

**Theorem 1.3 (Finite ground right-current cancellation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.ground_finite_right_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.ground_finite_right_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite ordered compositions cancel pairwise; the two surviving commutators are exactly the explicit finite correction.

**Theorem 1.4 (Native projected-ground consumer).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.projectedGround_finite_right_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.projectedGround_finite_right_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite cancellation is instantiated with correctedField slices and the actual tensor current on arbitrary original target inputs.

The finite step leaves the full signed inverse-convolution bridge, the exact projected ground-pair base and arbitrary-first transport open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.ground_finite_right_transport`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.projectedGround_current_ward`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.projectedGround_finite_right_transport`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockGroundRightCurrentTransport.projectedGround_positive_neutral`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentWard](LatticeHalfFockCurrentWard.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling](LatticeHalfFockPhysicalRescaling.md)
