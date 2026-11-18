# Selected-column Gram and common positive state

## Abstract

A selected column of an actual common center controls a joint residual Gram and yields one common positive state.

**Definition 1.1 (Canonical isometric Kraus column).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.J`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The column maps an input vector to the output and environment carrier using the canonical normalized Kraus family. The common-state construction uses its isometric compression.

**Definition 1.2 (Local channel adjoint).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.Phi`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.Phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compress the local matrix acting in the canonical Kraus representation. This is the local block action in the reference trace pairing.

**Definition 1.3 (Reference-amplified adjoint).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.PhiR`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.PhiR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply Phi blockwise to a complex joint matrix in the reference coordinates. The kernel estimate pairs this adjoint with the actual amplified channel.

**Definition 1.4 (Local matrix representation).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.pi`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.pi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The representation acts by the local matrix tensor the environment identity. The selected-column residual is formed in this representation.

**Definition 1.5 (Complementary Kraus projection).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.e`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.e` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defect projection is the identity minus J J adjoint. It gives the support of the selected Gram factor and its replacement after the polar step.

**Definition 1.6 (Joint adjoint defect).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.defectR`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.defectR` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the product of the two adjoint images from the adjoint image of Y Y adjoint. The trace test and the weighted energy defect use this matrix for Y and its adjoint.

**Theorem 1.7 (The reference adjoint preserves conjugate transpose).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.PhiR_star`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.PhiR_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite nonempty local carriers, every finite reference and arbitrary complex Y, PhiR of the conjugate transpose is the conjugate transpose of PhiR of Y. The Hilbert–Schmidt trace pairing and both Gram bounds use this equality.

**Definition 1.8 (Matrix units).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.E`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each pair of output indices defines the matrix with a single unit entry. The packed column uses all these matrix units.

**Definition 1.9 (A defect block for a matrix unit).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.Cblock`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.Cblock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The block is J adjoint times the represented matrix unit times the complementary projection e. The selected-column proof packs these blocks together.

**Definition 1.10 (The packed defect matrix).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.C`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Concatenate the Cblock matrices over the output index pairs. Its Gram matrix is the bound in the joint selected-column estimate.

**Definition 1.11 (The packed scalar residual).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.D`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Concatenate the residual blocks made from the chosen scalar family and the compressed matrix units. The selected-column estimate factors this matrix through C.

**Definition 1.12 (The uniform positive trace test).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.UniversalPositiveTraceTest`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.UniversalPositiveTraceTest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite reference, complex output joint matrix Y and positive definite input joint Z, bound the infimum of the traced left residual Gram over all complex reference centers by the scaled traced adjoint defect. The endpoint estimate supplies this premise at c/(1-c).

**Definition 1.13 (The weighted ordinary partial trace).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.stateCenter`

*Formalization.* `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.stateCenter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the ordinary partial trace after left multiplication by the embedded output state. In each reference block this is the trace of the output state times that block. The kernel estimate uses this one center with both Gram bounds.

**Theorem 1.14 (Positive semidefiniteness of the joint defect).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.defectR_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.defectR_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite channel between nonempty carriers, every finite reference and complex Y, the adjoint defect is positive semidefinite. The endpoint and all-parameter proofs take real trace pairings of this defect against positive joint bases.

**Theorem 1.15 (One scalar family for the entire basis Gram).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.selected_column_joint_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.selected_column_joint_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a and b be finite nonempty types, let Phi be an actual completely positive trace-preserving channel from a to b, and let k be a nonnegative real number. Its canonical normalized Kraus family defines an isometric column J, the representation pi(A)=A tensor I_Env, and the projection e=I-J J adjoint. The universal premise tests every finite reference and complex joint input against general matrix centers.

A selected matrix-unit column supplies a scalar family whose joint residual Gram is bounded by k times the actual defect Gram, including k=0. This joint bound supplies the rectangular factor used to construct the common state.

Pack the full matrix-unit basis into one selected column. The packed defect is C C adjoint. A general matrix center supplies the residual P, whose selected column is D. Its remaining columns form R and give P P adjoint=D D adjoint+R R adjoint. Adding the positive remainder yields the joint selected-column inequality without imposing sparsity on the center. The positive Gram remainder preserves the bound on the selected column.

The common-state theorem below uses this joint Gram bound. The final all-finite Umegaki coefficient equality remains open.

**Theorem 1.16 (One state and one ordinary partial-trace center).**

Lean statement: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.common_positive_state_scalarizer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.common_positive_state_scalarizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite nonempty input and output carriers, a canonical channel and its universal positive trace test produce one DensityState on the output carrier. The state is independent of the finite reference and the complex joint input.

For every finite reference, including the empty carrier, the center is the ordinary unnormalized weighted partial trace of the joint input. The same center satisfies both left and right residual Gram inequalities with the stated coefficient k. The construction permits singular states and uses no faithful-state, invertibility, unitary-polar, or dimension-normalization assumption.

Apply the existing Hilbert-space Douglas theorem on the Euclidean space indexed by a disjoint sum, then extract the heterogeneous block and project it with e. This supplies C T=D, e T=T and T adjoint T bounded by k I without dividing by k. The full complex matrix-unit expansion gives J adjoint pi(Z)(J-T)=Tr(tau Z) I, where tau(v,u)=x(u,v). Orthogonality gives Tr(tau)=1 and (J-T) adjoint (J-T)=I+T adjoint T.

The native singular polar supplier gives U adjoint tau=abs(tau) with U contractive. Finite trace-norm duality proves t=Tr(abs(tau)) at least one. Set sigma=abs(tau)/t and W=t inverse pi(U adjoint)(J-T). The correct compression uses Tr(tau Z U adjoint)=Tr(U adjoint tau Z), so it is Tr(sigma Z) I. Thus J adjoint W=I. For K=J-W, the positive congruence of I-t inverse squared pi(U U adjoint) proves K adjoint K bounded by T adjoint T. Support e K=K then earns K K adjoint bounded by k e.

Amplify this fixed K and W by the reference identity and reindex the Kronecker representation by the product associator. The compression is the blockwise trace pairing, exactly the weighted ordinary partial trace. Congruence of the supported Gram bound gives the first residual inequality. Hermiticity of sigma makes its center preserve adjoints; applying the first inequality to the adjoint input gives the second at the same center.

The kernel contraction uses both Gram bounds from this same state for the inverse direction of the amplified channel. The all-channel coefficient theorem, support and regularization steps, and final ratio comparison remain open.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.C`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.Cblock`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.D`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.E`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.J`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.Phi`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.PhiR`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.PhiR_star`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.UniversalPositiveTraceTest`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.common_positive_state_scalarizer`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.defectR`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.defectR_posSemidef`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.e`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.pi`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.selected_column_joint_gram`
- Truth anchor: `D5/S3/Quantum/Divergence/UniversalPositiveScalarizer.stateCenter`
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Basic](../Analysis/TraceClass/Basic.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Pairing](../Analysis/TraceClass/Pairing.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/Polar](../Analysis/TraceClass/Polar.md)
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Divergence/ScalarizerMatrixTransport](ScalarizerMatrixTransport.md)
- Dependency: [D5/S3/Quantum/Divergence/UniversalCommonCenter](UniversalCommonCenter.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
