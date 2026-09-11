# OrderedGridMemory

## Abstract

Geometric hard-core branching, exact certificates and their precise scope.

**Definition 1.1 (Square-grid coordinates).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.Point`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.Point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pairs of integers describe actual grid vertices in the frame of an east-facing incoming edge.

**Definition 1.2 (The three forward directions).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.direction`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.direction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three directions are straight, right and left. The fourth direction is the already-deleted parent.

**Definition 1.3 (All six local orderings).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.position`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.position` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The six rows specify the permutations SRL, SLR, RSL, RLS, LSR and LRS.

**Definition 1.4 (Ordered vertex deletions).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.deleted`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.deleted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Before following a child, delete the current vertex and all earlier neighbors. Including an already absent neighbor does not change the remaining domain.

**Definition 1.5 (Normalize the chosen incoming heading).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.recenter`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.recenter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An integer translation and quarter-turn put the child at the origin and its incoming heading east.

**Theorem 1.6 (Coordinate normalization preserves identity).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.recenter_injective`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.recenter_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the recentered vertices implies equality of both original integer coordinates.

**Definition 1.7 (The actual remaining finite domain).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.advance`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.advance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Delete vertices in the prescribed order and apply the same coordinate normalization to all remaining vertices.

**Definition 1.8 (Truncated geometric blockers).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.memoryStep`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.memoryStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Update the actual blocked set and retain only points within a Manhattan disk. Forgotten blockers are discarded permanently.

**Theorem 1.9 (Geometric soundness for every radius).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.advance_disjoint_memoryStep`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.advance_disjoint_memoryStep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Disjointness between available vertices and recorded blockers is preserved by deletion, recentering and truncation. The proof uses injectivity of the actual coordinate map.

**Definition 1.10 (Count actual domain paths).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A child is available exactly when its grid vertex belongs to the actual finite domain. Missing table entries use a fallback state and never suppress an available child by definition.

**Theorem 1.11 (Uniform finite-domain simulation).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount_le_pathCount`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount_le_pathCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact table rejection and geometric-successor identities imply domination of every finite-domain path count at every depth. RadiusThreeCertificates proves these finite obligations for its concrete table.

**Theorem 1.12 (Only the selected actions need closure).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount_le_pathCount_selected`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount_le_pathCount_selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing geometric induction is generalized to the actions actually chosen by the controller. The original all-action theorem applies it with its public statement unchanged. AdaptiveRadiusFourCertificates consumes the selected-action version on its complete controller-reachable table.

The sources were logically reviewed and the concrete certificates independently replayed using exact integers. Lean elaboration, axiom-print execution and Scribe emission were not performed in the authoring runtime. These candidate sources do not assert an improved global zero-free threshold.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.Point`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.advance`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.advance_disjoint_memoryStep`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.deleted`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.direction`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.memoryStep`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount_le_pathCount`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.orderedCount_le_pathCount_selected`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.position`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.recenter`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory.recenter_injective`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/BranchingPotential](BranchingPotential.md)
