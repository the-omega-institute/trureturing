# Geometric Memory Refinement

## Abstract

Geometric hard-core memory, exact path semantics and integer certificates.

**Definition 1.1 (The geometric transition).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.geometricStep`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.geometricStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A child is present exactly when its direction is outside the recorded blocked set. Its successor is the existing radius-truncated geometric update.

**Theorem 1.2 (Monotone retained geometry).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.memoryStep_mono`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.memoryStep_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Increasing the blocked set and radius preserves blocker inclusion under the same ordering and direction.

**Theorem 1.3 (Common history-based ordering).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.history_count_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.history_count_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Larger memory has no more descendants at any depth under the same history-based policy. Independently chosen state policies are outside this statement.

**Definition 1.4 (Retain the coarse controller state).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.coupledStep`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.coupledStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep both blocked sets. The refined set decides availability; both receive the same action. The coarse state is not recovered by projecting the fine state.

**Theorem 1.5 (Transport an arbitrary coarse controller).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.coupled_count_le_coarse`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.coupled_count_le_coarse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The controller may depend on its coarse state and complete direction history. The coupled implementation reads the same inputs and never increases path counts.

**Theorem 1.6 (Exact finite-presentation semantics).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.fixed_presentation_count`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.fixed_presentation_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direction-preserving transition equality gives equality of all fixed-order counts. Only the selected order requires closure. Directions retain their multiplicities. RadiusFourCertificates supplies a concrete consumer.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.coupledStep`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.coupled_count_le_coarse`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.fixed_presentation_count`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.geometricStep`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.history_count_antitone`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryRefinement.memoryStep_mono`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory](OrderedGridMemory.md)
