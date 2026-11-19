# The Mixed Jacobi Identity on the Original Fixed Sector

## Abstract

The Mixed Jacobi Identity on the Original Fixed Sector

**Theorem 1.1 (Source modes under the graded pairing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceModeTransport.source_mode_of_oppositeDual`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceModeTransport.source_mode_of_oppositeDual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original source BPZ identity transports the opposite action on a grade dual to the actual lattice field mode.

**Theorem 1.2 (Finite sums of source grades).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceModeTransport.restore_fixed_source_opposite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceModeTransport.restore_fixed_source_opposite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transport holds on the full restricted dual by applying the graded relation to every direct-sum component.

**Theorem 1.3 (Mixed Jacobi on the fixed sector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceModeTransport.original_mixed_jacobi`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceModeTransport.original_mixed_jacobi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one fixed and two twisted inputs, apply the original inverse of the pairing to the three finite coefficient sums. The first right channel becomes the actual fixed source action on the reconstructed coefficient.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceModeTransport.original_mixed_jacobi`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceModeTransport.restore_fixed_source_opposite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalSourceModeTransport.source_mode_of_oppositeDual`
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/AllStateTranspose](../SourceBPZ/AllStateTranspose.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMCoefficients](OriginalFourMCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMContraction](OriginalFourMContraction.md)
