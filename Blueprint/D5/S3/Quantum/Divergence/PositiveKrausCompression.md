# Positive replacement of the Kraus compression

## Abstract

The selected-column Gram controls a positive replacement of the canonical local Kraus compression.

**Definition 1.1 (Canonical isometric Kraus column).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.J`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The column maps an input vector to the output and environment carrier using the canonical normalized Kraus family. The common-state construction uses its isometric compression.

**Definition 1.2 (Local channel adjoint).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.Phi`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.Phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compress the local matrix acting in the canonical Kraus representation. This is the local block action in the reference trace pairing.

**Definition 1.3 (Reference-amplified adjoint).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.PhiR`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.PhiR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply Phi blockwise to a complex joint matrix in the reference coordinates. The kernel estimate pairs this adjoint with the actual amplified channel.

**Definition 1.4 (Local matrix representation).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.pi`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.pi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The representation acts by the local matrix tensor the environment identity. The selected-column residual is formed in this representation.

**Definition 1.5 (Complementary Kraus projection).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.e`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.e` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defect projection is the identity minus J J adjoint. It gives the support of the selected Gram factor and its replacement after the polar step.

**Definition 1.6 (Joint adjoint defect).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.defectR`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.defectR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the product of the two adjoint images from the adjoint image of Y Y adjoint. The trace test and the weighted energy defect use this matrix for Y and its adjoint.

**Theorem 1.7 (The reference adjoint preserves conjugate transpose).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.PhiR_star`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PositiveKrausCompression.PhiR_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite nonempty local carriers, every finite reference and arbitrary complex Y, PhiR of the conjugate transpose is the conjugate transpose of PhiR of Y. The Hilbert–Schmidt trace pairing and both Gram bounds use this equality.

**Definition 1.8 (Matrix units).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.E`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each pair of output indices defines the matrix with a single unit entry. The packed column uses all these matrix units.

**Definition 1.9 (A defect block for a matrix unit).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.Cblock`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.Cblock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The block is J adjoint times the represented matrix unit times the complementary projection e. The selected-column proof packs these blocks together.

**Definition 1.10 (The packed defect matrix).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.C`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Concatenate the Cblock matrices over the output index pairs. Its Gram matrix is the bound in the joint selected-column estimate.

**Definition 1.11 (The packed scalar residual).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.D`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Concatenate the residual blocks made from the chosen scalar family and the compressed matrix units. The selected-column estimate factors this matrix through C.

**Definition 1.12 (The uniform positive trace test).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.UniversalPositiveTraceTest`

*Formalization.* `D5/S3/Quantum/Divergence/PositiveKrausCompression.UniversalPositiveTraceTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite reference, complex output joint matrix Y and positive definite input joint Z, bound the infimum of the traced left residual Gram over all complex reference centers by the scaled traced adjoint defect. The endpoint estimate supplies this premise at c/(1-c).

**Theorem 1.13 (One scalar family for the entire basis Gram).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.selected_column_joint_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PositiveKrausCompression.selected_column_joint_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and b be finite nonempty types, let Phi be an actual completely positive trace-preserving channel from a to b, and let k be a nonnegative real number. Its canonical normalized Kraus family defines an isometric column J, the representation pi(A)=A tensor I_Env, and the projection e=I-J J adjoint. The universal premise tests every finite reference and complex joint input against general matrix centers.

A selected matrix-unit column supplies a scalar family whose joint residual Gram is bounded by k times the actual defect Gram, including k=0. This joint bound supplies the rectangular factor used to construct the common state.

Pack the full matrix-unit basis into one selected column. The packed defect is C C adjoint. A general matrix center supplies the residual P, whose selected column is D. Its remaining columns form R and give P P adjoint=D D adjoint+R R adjoint. Adding the positive remainder yields the joint selected-column inequality without imposing sparsity on the center. The positive Gram remainder preserves the bound on the selected column.

The positive Kraus compression uses this joint Gram bound. The final all-finite Umegaki coefficient equality remains open.

**Theorem 1.14 (Positive trace-one Kraus compression).**

Lean statement: `D5/S3/Quantum/Divergence/PositiveKrausCompression.common_positive_state_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/PositiveKrausCompression.common_positive_state_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal trace test supplies a rectangular Douglas factor supported on the Kraus complement. The singular polar factor and finite trace-norm bound give a normalized positive state and a replacement compression with the same supported Gram bound. UniversalPositiveScalarizer uses this fixed compression on every reference.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.C`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.Cblock`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.D`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.E`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.J`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.Phi`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.PhiR`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.PhiR_star`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.UniversalPositiveTraceTest`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.common_positive_state_compression`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.defectR`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.e`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.pi`
- Truth anchor: `D5/S3/Quantum/Divergence/PositiveKrausCompression.selected_column_joint_gram`
- Dependency: [D5/S3/HilbertOperators/DouglasLemma](../../HilbertOperators/DouglasLemma.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Basic](../Analysis/TraceClass/Basic.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Pairing](../Analysis/TraceClass/Pairing.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Polar](../Analysis/TraceClass/Polar.md)
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Divergence/UniversalCommonCenter](UniversalCommonCenter.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
