# Finite Complete Pick Interpolation Property

## Abstract

Matrix-valued finite Pick data define complete kernel contractivity and a precise complete interpolation property.

**Definition 1.1 (Matrix-valued block Pick matrix).**

Lean statement: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.operatorPickMatrix`

*Formalization.* `D5/S3/Weil/Pick/CompletePickInterpolationProperty.operatorPickMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each node pair contributes the kernel scalar times the block defect from the two target matrices.

**Definition 1.2 (Consistent repeated-node data).**

Lean statement: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.ConsistentMatrixInterpolationData`

*Formalization.* `D5/S3/Weil/Pick/CompletePickInterpolationProperty.ConsistentMatrixInterpolationData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Repeated interpolation nodes are required to carry identical matrix values.

**Definition 1.3 (Matrix interpolation predicate).**

Lean statement: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.InterpolatesMatrixData`

*Formalization.* `D5/S3/Weil/Pick/CompletePickInterpolationProperty.InterpolatesMatrixData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A multiplier interpolates the data when it takes every prescribed value at its node.

**Definition 1.4 (Complete kernel contractivity at fixed size).**

Lean statement: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.IsCompletelyKernelContractive`

*Formalization.* `D5/S3/Weil/Pick/CompletePickInterpolationProperty.IsCompletelyKernelContractive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every finite block Pick matrix sampled from the matrix-valued function is positive semidefinite.

**Definition 1.5 (Finite complete Pick property).**

Lean statement: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.HasCompletePickInterpolationProperty`

*Formalization.* `D5/S3/Weil/Pick/CompletePickInterpolationProperty.HasCompletePickInterpolationProperty` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every consistent positive finite block Pick datum admits a completely kernel-contractive interpolant.

**Theorem 1.6 (Zero-kernel block Pick matrices vanish).**

Lean statement: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.operatorPickMatrix_zeroKernel`

*Formalization.* `D5/S3/Weil/Pick/CompletePickInterpolationProperty.operatorPickMatrix_zeroKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every matrix-valued Pick matrix over the zero kernel is the zero matrix.

**Theorem 1.7 (Every matrix multiplier contracts the zero kernel).**

Lean statement: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.every_matrix_multiplier_contracts_zeroKernel`

*Formalization.* `D5/S3/Weil/Pick/CompletePickInterpolationProperty.every_matrix_multiplier_contracts_zeroKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vanishing block Pick matrices make every matrix-valued function completely contractive over the zero kernel.

**Definition 1.8 (Classical consistent-data extension).**

Lean statement: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.extendConsistentMatrixData`

*Formalization.* `D5/S3/Weil/Pick/CompletePickInterpolationProperty.extendConsistentMatrixData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite consistent partial matrix assignment is extended by choosing a matching node when one exists.

**Theorem 1.9 (The extension interpolates consistent data).**

Lean statement: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.extendConsistentMatrixData_interpolates`

*Formalization.* `D5/S3/Weil/Pick/CompletePickInterpolationProperty.extendConsistentMatrixData_interpolates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Repeated-node consistency makes the chosen finite extension independent of the selected witness.

**Theorem 1.10 (The zero kernel has the complete property).**

Lean statement: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.zeroKernel_hasCompletePickInterpolationProperty`

*Formalization.* `D5/S3/Weil/Pick/CompletePickInterpolationProperty.zeroKernel_hasCompletePickInterpolationProperty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero kernel provides a fully checked inhabited model of the finite matrix interpolation definition.

## References

- Truth anchor: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.operatorPickMatrix`
- Truth anchor: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.ConsistentMatrixInterpolationData`
- Truth anchor: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.InterpolatesMatrixData`
- Truth anchor: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.IsCompletelyKernelContractive`
- Truth anchor: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.HasCompletePickInterpolationProperty`
- Truth anchor: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.operatorPickMatrix_zeroKernel`
- Truth anchor: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.every_matrix_multiplier_contracts_zeroKernel`
- Truth anchor: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.extendConsistentMatrixData`
- Truth anchor: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.extendConsistentMatrixData_interpolates`
- Truth anchor: `D5/S3/Weil/Pick/CompletePickInterpolationProperty.zeroKernel_hasCompletePickInterpolationProperty`
- Dependency: [D5/S3/Weil/Pick/DeBrangesRovnyakKernel](DeBrangesRovnyakKernel.md)
