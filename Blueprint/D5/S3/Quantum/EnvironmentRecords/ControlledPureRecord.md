# Controlled pure records and address dephasing

## Abstract

Exact operational distance between controlled readout and complete address dephasing.

The address is Fin 2. Each record Wᵢ is a matrix of amplitudes with finite visible row index O and hidden column index E. Normalization means tr(WᵢWᵢ†) = 1 for each address. Write C = W₀W₁† for the cross reduction. The second preparation stores an additional orthogonal copy of the address in the hidden register.

**Theorem 1.1 (The controlled preparation is isometric).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.controlledIsometry_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.controlledIsometry_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With both records normalized, V sends |i⟩ to |i⟩ tensored with its record vector and satisfies V†V = I in address, visible, hidden order.

**Theorem 1.2 (Trace out the hidden register).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutMap_eq_partialTrace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutMap_eq_partialTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output on the address and visible register is the partial trace of VXV† over E for every address matrix X.

**Theorem 1.3 (The ordinary channel implements the readout map).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutChannel_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutChannel_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized records and a visible index with decidable equality, readoutChannel is the canonical completely positive trace-preserving channel. Its matrix action is readoutMap.

**Theorem 1.4 (The address blocks of the joint output).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutMap_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutMap_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The (i,j) address block of the readout is Xᵢⱼ WᵢWⱼ†. In particular the (0,1) block is X₀₁ C, and the (1,0) block is X₁₀ C†.

**Theorem 1.5 (An orthogonal hidden address copy dephases the readout).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.dephased_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.dephased_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If both records have the same visible reduction R, the copy readout gives diagonal blocks Xᵢᵢ R and zero off-diagonal blocks.

**Theorem 1.6 (The visible register has the same output).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.visible_agreement`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.visible_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the common-reduction hypothesis, tracing out the address from either readout gives tr(X) R for every X. A trace-one input therefore gives R in both cases.

**Theorem 1.7 (The address alone retains the scalar overlap).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.trace_visible_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.trace_visible_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tracing out the visible register multiplies each input entry Xᵢⱼ by tr(WᵢWⱼ†). The trace of C is the scalar factor on the (0,1) address entry.

**Theorem 1.8 (Exact norm of the reference-amplified difference).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.referenceDifference_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.referenceDifference_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized records, a finite reference with decidable equality, and every complex joint matrix X, the output difference has trace norm ‖C‖₁(‖X₀₁‖₁ + ‖X₁₀‖₁). Here X₀₁ and X₁₀ are matrices on the reference. The output has only off-diagonal address blocks, given by tensoring these input blocks with C and C† respectively.

**Theorem 1.9 (Uniform induced trace-norm bound).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.referenceDifference_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.referenceDifference_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each such finite reference dimension, the amplified output difference has trace norm at most ‖C‖₁‖X‖₁ for every joint matrix X. Half the difference of X and its conjugate by the diagonal address sign is its off-diagonal part. The triangle inequality bounds its norm by ‖X‖₁.

**Theorem 1.10 (The balanced address input attains the separation).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutDifference_plus`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutDifference_plus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projector onto (|0⟩ + |1⟩)/√2 produces output difference of trace norm ‖C‖₁ without a reference.

**Theorem 1.11 (Every reference state gives an attaining product input).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.referenceDifference_product`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.referenceDifference_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For normalized records, the product of any finite reference density state and the balanced address projector attains the amplified bound.

**Theorem 1.12 (Exact unhalved diamond distance).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.diamondDistance_readout_dephased`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.diamondDistance_readout_dephased` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2009). *Semidefinite Programs for Completely Bounded Norms*. DOI: [10.4086/toc.2009.v005a011](https://doi.org/10.4086/toc.2009.v005a011). URL: <https://theoryofcomputing.org/articles/v005a011/>.

*Commentary.*

For normalized records, the diamond distance between the readout channel and its hidden-address-copy version is ‖C‖₁. The finite-channel distance takes the supremum of output trace-norm differences on joint density inputs over all finite reference dimensions. The uniform bound and balanced input give equality. Watrous supplies the norm and channel-discrimination framework.

**Theorem 1.13 (A common reconstruction has a worst-case error).**

Lean statement: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.reconstruction_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.reconstruction_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the balanced address input, any single matrix proposed for both joint outputs has maximum trace-norm error at least ‖C‖₁/2 by the triangle inequality.

These are static finite channels. Physical dynamics and any heat or work assertion require separate assumptions.

## References

- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.controlledIsometry_isometry`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.dephased_apply`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.diamondDistance_readout_dephased`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutChannel_apply`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutDifference_plus`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutMap_apply`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.readoutMap_eq_partialTrace`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.reconstruction_lower`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.referenceDifference_le`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.referenceDifference_norm`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.referenceDifference_product`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.trace_visible_apply`
- Truth anchor: `D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord.visible_agreement`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks](../Entanglement/PermutationCriteria/BellBlocks.md)
- Dependency: [D5/S3/Quantum/EnvironmentRecords](../EnvironmentRecords.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/TraceNormTensorProduct](../Foundation/TraceNormTensorProduct.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/RootTrace](../Measurement/Auric/RootTrace.md)
