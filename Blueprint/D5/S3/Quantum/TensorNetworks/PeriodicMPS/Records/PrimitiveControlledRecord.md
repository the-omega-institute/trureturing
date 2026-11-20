# The controlled channel of the primitive periodic collision

## Abstract

The common adjacent-pair state and the exact separation of two address-retaining channels.

The address values 0 and 1 select the false and true cores of the checked primitive periodic binary bond-two collision. Flatten the normalized ring amplitudes using sites zero and one as the visible row index and the remaining m sites as the hidden column index. The total ring length is n = 2 + m. The channel statements use m ≥ 5.

**Theorem 1.1 (Both records reduce to the same adjacent pair).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.records_common_visible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.records_common_visible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For m ≥ 5, the reduction of either record onto the adjacent pair is the common trace-one collisionMarginal. The supplier collisionFlattening_common_visible uses PeriodicMPSPrimitiveCollision.primitive_two_site_collision at n = 2 + m.

**Theorem 1.2 (The cross reduction of the literal record pair).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.records_cross`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.records_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each m, the zero record times the adjoint of the one record is the matrix collisionNormalizedCross(m) from PeriodicMPSPrimitiveCollisionOverlap, by collisionFlattening_cross. Write Cₘ for this matrix.

**Theorem 1.3 (The joint channel is the actual partial trace).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.jointChannel_eq_partialTrace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.jointChannel_eq_partialTrace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The controlled isometry prepares the normalized periodic ring while keeping the address. Tracing out the last m sites gives jointChannel on the address and first two sites.

**Theorem 1.4 (The comparator completely dephases the address).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.dephasedChannel_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.dephasedChannel_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each address matrix X, dephasedChannel gives diagonal blocks Xᵢᵢ collisionMarginal and zero off-diagonal blocks.

**Theorem 1.5 (The retained address and pair carry cross coherence).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.jointChannel_coherence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.jointChannel_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The (0,1) address block of jointChannel applied to X is X₀₁ Cₘ on the observed pair.

**Theorem 1.6 (The adjacent-pair observer sees the same state).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.visible_pair_agrees`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.visible_pair_agrees` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every address matrix X, discarding the address from either readout yields tr(X) collisionMarginal. On every density input the adjacent pair is therefore exactly the same for both channels.

**Theorem 1.7 (The address alone carries the scalar overlap).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.address_coherence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.address_coherence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m and address matrix X, tracing out the visible pair in the joint readout gives the (0,1) entry collisionNormalizedOverlap(2 + m) X₀₁.

**Theorem 1.8 (The operational bound holds with every finite reference).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.amplified_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.amplified_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m ≥ 5 and every joint input matrix X with a finite reference with decidable equality, the trace norm of the amplified channel difference is at most ‖Cₘ‖₁‖X‖₁.

**Theorem 1.9 (A balanced address input attains the separation).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.plus_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.plus_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The balanced address projector gives readout outputs separated by ‖Cₘ‖₁ in trace norm without a reference.

**Theorem 1.10 (An arbitrary reference state preserves attainment).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.product_attains`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.product_attains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m ≥ 5 the product of the balanced address projector and any finite reference density state attains an amplified output separation of ‖Cₘ‖₁.

**Theorem 1.11 (Exact unhalved diamond distance at each ring length).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.jointChannel_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.jointChannel_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2009). *Semidefinite Programs for Completely Bounded Norms*. DOI: [10.4086/toc.2009.v005a011](https://doi.org/10.4086/toc.2009.v005a011). URL: <https://theoryofcomputing.org/articles/v005a011/>.

*Commentary.*

At every ring length n = 2 + m ≥ 7, the unhalved diamond distance from jointChannel to dephasedChannel is ‖Cₘ‖₁. This evaluates the supremum with finite references for the actual primitive collision. Critch and Morton supply the MPS marginal setting, and Watrous supplies the distance convention.

**Theorem 1.12 (An adjacent-pair-only prediction has a worst-case error).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.reconstruction_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.reconstruction_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the balanced address input, any single proposed joint output has maximum trace-norm error at least ‖Cₘ‖₁/2 across the two readout maps. With m ≥ 5, their identical adjacent-pair output gives the same data to a prediction rule that only has access to that pair.

The ring length is a size parameter. A physical preparation or evolution and any heat or work assertion require separate assumptions.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.address_coherence`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.amplified_bound`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.dephasedChannel_apply`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.jointChannel_coherence`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.jointChannel_distance`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.jointChannel_eq_partialTrace`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.plus_attains`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.product_attains`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.reconstruction_lower`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.records_common_visible`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.records_cross`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveControlledRecord.visible_pair_agrees`
- Dependency: [D5/S3/Quantum/EnvironmentRecords/ControlledPureRecord](../../../EnvironmentRecords/ControlledPureRecord.md)
