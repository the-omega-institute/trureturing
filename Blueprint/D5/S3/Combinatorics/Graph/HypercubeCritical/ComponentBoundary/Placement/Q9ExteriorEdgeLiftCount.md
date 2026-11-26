# Parallel flips of occupied edges

## Abstract

Parallel flips force edges inside the exterior of a balanced cubic support.

**Theorem 1.1 (An exterior with at least 104 edges).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ExteriorEdgeLiftCount.exterior_edges_ge_one_hundred_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ExteriorEdgeLiftCount.exterior_edges_ge_one_hundred_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a balanced induced cubic support on at least 48 vertices. Suppose at least 45 exterior vertices have exactly two support neighbors and at least two exterior neighbors outside that distinguished set. Each occupied edge admits four parallel flips into the exterior. Even exterior degree bounds the number of lifts of an exterior edge by eight. Every edge incident to the distinguished set has at most two lifts. The hypotheses force at least 90 such edges. Counting the lifts yields the lower bound of 104 exterior edges.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ExteriorEdgeLiftCount.exterior_edges_ge_one_hundred_four`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance](CubicContactDistance.md)
