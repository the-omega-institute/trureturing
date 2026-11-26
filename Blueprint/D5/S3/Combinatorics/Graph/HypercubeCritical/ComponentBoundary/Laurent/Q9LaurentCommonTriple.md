# Projecting away a common direction triple

## Abstract

A common direction triple gives threefold fibers and a descended integer height.

**Theorem 1.1 (Every occupied projection fiber is a single three-leaf star).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonTriple.exists_star_over_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonTriple.exists_star_over_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If each selected vertex has a unique neighbor of the common direction type, two such centers in the same fiber would have disjoint sets of three leaves. A parity half of a three-cube has four vertices, so a nonempty fiber consists of the leaves of one center.

**Theorem 1.2 (The exponent on the six remaining axes is constant on each fiber).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonTriple.exponent_eq_outside`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonTriple.exponent_eq_outside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two vertices in the same fiber share the direction-triple center. The Laurent two-step gain has support in the removed triple, so the other six height coordinates are equal. The Laurent direction partition gives the required unique neighbor whenever the common triple occurs at every selected vertex.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonTriple.exists_star_over_projection`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonTriple.exponent_eq_outside`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition](../Q9LaurentGainPartition.md)
