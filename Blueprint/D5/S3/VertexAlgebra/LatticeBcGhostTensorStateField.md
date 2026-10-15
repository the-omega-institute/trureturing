# Compiled bridges

## Abstract

Actual lattice matter tensor bc state-field on the original carrier.

TensorProduct.lift composes the accepted finite integer-mode convolution with the actual lattice and bc state fields. The matter factor is even; parity is carried by the bc factor.

**Theorem 1.1 (All-state creation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Creation is proved on arbitrary algebraic tensor states by tensor induction.

**Theorem 1.2 (Vacuum creativity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creativity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creativity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonnegative mode vanishes on the actual tensor vacuum.

**Theorem 1.3 (Actual parity decomposition).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.parity_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.parity_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second-factor parity projections are idempotent, orthogonal, and exhaustive on arbitrary tensor states.

**Theorem 1.4 (Original translation bridge).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.translation_original`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.translation_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains both Gram inverse equations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.parity_decomposition`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creativity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.translation_original`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
- Dependency: [D5/S3/VertexAlgebra/VertexOperatorTensorProduct](VertexOperatorTensorProduct.md)
