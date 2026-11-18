# Symmetric Twelve Capacity

## Abstract

Symmetric Twelve Capacity

Count real incidences between cycle points and all actual lows. On a high twelve-cycle, girth forces a low with two cycle neighbors onto a diameter; adjacent occupied diameters are forbidden, so at most three actual lows are internal. The resulting incidence bound contradicts eight total lows. Finite checks concern only twelve-cycle indices.

This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim.

**Theorem 1.1 (incidence capacity).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.incidence_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.incidence_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite sets and a relation, if every left point has a related right point and each right point has at most two related left points, left cardinality is at most right cardinality plus the number of right points with two related left points.

**Definition 1.2 (cycleVertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.cycleVertices`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.cycleVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image of the twelve indexed cycle points in the actual vertex type.

**Definition 1.3 (internalLows).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.internalLows`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.internalLows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All actual degree-two vertices with at least two neighbors among those twelve actual cycle points.

**Theorem 1.4 (internal low count le three).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.internal_low_count_le_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.internal_low_count_le_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the actual bipartite graph with degrees two or three, independent lows and girth at least eight, an injective high twelve-cycle of full high degree two has at most three internal actual lows. The parity side hypotheses and all original graph assumptions are retained.

**Theorem 1.5 (cycle capacity bound).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.cycle_capacity_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.cycle_capacity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective twelve-point high family with full high degree two needs at least twelve incidences from all actual lows, counted with one extra unit for each internal low. This capacity statement assumes degree two or three and independent lows; it does not add bipartiteness, girth or cycle adjacency.

**Theorem 1.6 (twelve cycle impossible).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.twelve_cycle_impossible`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.twelve_cycle_impossible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If exactly eight actual lows coexist with the stated bipartite high twelve-cycle, its internal-low bound and incidence capacity force 12 <= 8 + 3, a contradiction. The exact original hypotheses remain explicit.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.cycleVertices`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.cycle_capacity_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.incidence_capacity`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.internalLows`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.internal_low_count_le_three`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.twelve_cycle_impossible`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPartners](SymmetricLowPartners.md)
