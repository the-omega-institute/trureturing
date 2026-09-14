# Uniform Block Bounds from Complete Prefixes

## Abstract

Geometric hard-core memory, exact path semantics and integer certificates.

**Theorem 1.1 (Complete paths are covered by truncated memory).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryBlockBounds.complete_count_le_memory`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MemoryBlockBounds.complete_count_le_memory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every depth and common history-based policy, inclusion of initial blockers gives an upper bound on complete-process counts by truncated-memory counts.

**Theorem 1.2 (A complete prefix bounds every later depth).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryBlockBounds.fixed_order_block_bound`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MemoryBlockBounds.fixed_order_block_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix one relative ordering. For r at least k and at least one, every initial blocker set containing the parent satisfies the explicit bound at depth q times k plus s. Its coefficient is the actual complete depth-k root count raised to q, times three raised to s. Parent retention, uniform continuation domination and finite-horizon exactness supply the proof. The theory derives fixed-order growth-rate completeness from this bound; the limit theorem is not separately elaborated here.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryBlockBounds.complete_count_le_memory`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryBlockBounds.fixed_order_block_bound`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/MemoryLightCone](MemoryLightCone.md)
