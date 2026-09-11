# Finite-Depth Exactness of Geometric Memory

## Abstract

Geometric hard-core memory, exact path semantics and integer certificates.

**Definition 1.1 (Manhattan radius).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.gridRadius`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.gridRadius` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The radius is the sum of the natural absolute values of the integer coordinates.

**Theorem 1.2 (Finite propagation speed).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.recenter_radius_bound`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.recenter_radius_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every old radius is at most the recentered radius plus one. The proof uses the integer triangle inequality and the actual three coordinate maps.

**Definition 1.3 (Local blocker agreement).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.AgreeWithin`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.AgreeWithin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Membership agrees for every point in the specified disk; the sets may differ arbitrarily outside it.

**Theorem 1.4 (Agreement on the smaller light cone).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.memoryStep_agreeWithin`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.memoryStep_agreeWithin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement through radius n plus one implies agreement through radius n after the same update, when both retention radii are at least n.

**Definition 1.5 (Complete blocker accumulation).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.completeStep`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.completeStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the same deletion and recentering without forgetting any old blocker.

**Theorem 1.6 (Exact complete counts within the horizon).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.finite_horizon_exact`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.finite_horizon_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a common history-based ordering, radius at least n reproduces the complete depth-n count whenever initial blockers agree through radius n. This finite-depth statement alone does not interchange radius and depth limits.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.AgreeWithin`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.completeStep`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.finite_horizon_exact`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.gridRadius`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.memoryStep_agreeWithin`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/MemoryLightCone.recenter_radius_bound`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/MemoryRefinement](MemoryRefinement.md)
