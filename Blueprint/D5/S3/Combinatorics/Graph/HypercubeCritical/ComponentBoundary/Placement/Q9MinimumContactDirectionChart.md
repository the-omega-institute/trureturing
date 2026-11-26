# Eighteen endpoints with the same translated vertex

## Abstract

A lower bound for closest endpoints without shared directions.

**Theorem 1.1 (Eighteen endpoints when all closest pairs have disjoint directions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumContactDirectionChart.eighteen_endpoints_of_fixed_direction_origin`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumContactDirectionChart.eighteen_endpoints_of_fixed_direction_origin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let both supports be balanced induced cubic sets in the nine-cube with mutual separation at least three. Assume every cross-pair at distance three has disjoint occupied direction triples. Each attained translation value then has at least eighteen endpoints in the second support. Translate each closest endpoint by its three occupied directions. Within a fixed translation value, its direction triple determines the vertex. An occurring pair of directions represents an occupied midpoint with three neighbors. The two-step exchanges supply at least five neighboring triples at each endpoint. The partition of the neighbor directions forces their new axes to be distinct. These properties supply the face restrictions of the eighteen-triple bound. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9MinimumContactDirectionChart.eighteen_endpoints_of_fixed_direction_origin`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/DistanceThreeTripleFamilyBound](DistanceThreeTripleFamilyBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedDirections](Q9DistanceThreeUnsharedDirections.md)
