# Shortest paths through the two exteriors

## Abstract

Unshared distance-three contacts force at least 45 active rows per side and 162 crossing edges.

**Theorem 1.1 (Active vertices and crossing edges).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeCrossingCount.active_card_and_crossing_darts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeCrossingCount.active_card_and_crossing_darts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume balanced induced cubic supports at mutual separation at least three, with a distance-three contact and disjoint occupied directions at every such contact. Assume also two support neighbors at each active exterior vertex. Each side has at least 18 closest endpoints and each endpoint reaches at least five active vertices. Counting these incidences forces 45 active vertices per side. Each closest endpoint has at least six contact triples. Each closest pair gives six shortest paths, while each crossing edge can serve as the middle edge of at most four of them. This forces 162 crossing edges.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeCrossingCount.active_card_and_crossing_darts`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeActiveBoundary](Q9DistanceThreeActiveBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumContactDirectionChart](Q9MinimumContactDirectionChart.md)
