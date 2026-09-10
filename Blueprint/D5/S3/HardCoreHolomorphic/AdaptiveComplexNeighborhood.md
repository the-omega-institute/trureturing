# AdaptiveComplexNeighborhood

## Abstract

Explicit holomorphic hard-core coordinates and uniform complex neighborhoods.

**Theorem 1.1 (actual coefficient bounds).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.actual_coefficient_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.actual_coefficient_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The analytic estimate uses this additional exact bound on the same payload. The lower bound and slope sign are reused from the existing full-box certificate.

**Definition 1.2 (Pruning).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.Pruning`

*Formalization.* `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.Pruning` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A subset of actual geometric children. The root is separately treated.

**Definition 1.3 (childType).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.childType`

*Formalization.* `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.childType` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Total accessor, used only on genuine children by Pruning.

**Definition 1.4 (Omega).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.Omega`

*Formalization.* `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.Omega` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Explicit open tube around each actual type's compact real chart image.

**Definition 1.5 (ActivityTube).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.ActivityTube`

*Formalization.* `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.ActivityTube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One open activity neighborhood, independent of graph size and recursion depth.

**Definition 1.6 (adaptiveMap).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.adaptiveMap`

*Formalization.* `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.adaptiveMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual transformed map for the supplied geometric parent and child subset.

**Theorem 1.7 (neighborhoods open).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.neighborhoods_open`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.neighborhoods_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed message and activity domains really are open.

**Theorem 1.8 (adaptive uniform invariant).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.adaptive_uniform_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.adaptive_uniform_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual type and every allowed pruning has the same invariant complex neighborhood. Its widths are explicit: delta=10^-20, epsilon=10^-30. No existence, Lipschitz, holomorphy or complex-invariance premise is supplied.

**Theorem 1.9 (omega chart inverse).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.omega_chart_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.omega_chart_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The principal logarithm is the true inverse throughout each constructed message neighborhood. Imaginary phase wrapping is excluded by the actual width.

**Theorem 1.10 (adaptive holomorphic recovery).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.adaptive_holomorphic_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.adaptive_holomorphic_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the constructed neighborhood, the map is jointly holomorphic and its inverse coordinate is exactly the hard-core vacancy, with both poles excluded.

**Theorem 1.11 (four child root nonzero).**

Lean statement: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.four_child_root_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.four_child_root_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Four root factors need nonvanishing, not a three-child contraction claim. Every first child may use the already-owned initial type zero.

## References

- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.ActivityTube`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.Omega`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.Pruning`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.actual_coefficient_bounds`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.adaptiveMap`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.adaptive_holomorphic_recovery`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.adaptive_uniform_invariant`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.childType`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.four_child_root_nonzero`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.neighborhoods_open`
- Truth anchor: `D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood.omega_chart_inverse`
- Dependency: [D5/S3/HardCoreHolomorphic/InvariantTube](InvariantTube.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages](../StatisticalMechanics/HardCore/AdaptiveAffineMessages.md)
