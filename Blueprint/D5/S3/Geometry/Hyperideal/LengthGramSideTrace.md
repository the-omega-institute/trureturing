# A cyclic side trace is an original edge segment

## Abstract

For the six-length coefficient body, the simultaneous zero trace of one coordinate side support and the matching cyclic edge support is exactly the closed segment joining the two corresponding original endpoints.

Fix positive lengths in the order 01, 02, 03, 23, 13, 12. For a side label `k`, let the side support be `x_k = 0`. The cyclic supports alternate coordinate supports and Gram-row supports along the three remaining labels. Each trace is taken inside the original cut body.

**Theorem 1.1 (The cyclic side trace is a closed original edge).**

$$cycleEdgeHull$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramSideTrace.cycle_edge_hull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original endpoint lies in the nonpositive support halfspaces. The endpoint support classification shows that the two simultaneous zero conditions select exactly the two endpoints listed by the cyclic order. The common zero-trace convex-hull theorem therefore reduces the intersection to the convex hull of those two points, namely their closed segment.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramSideTrace.cycle_edge_hull`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramPolytope](LengthGramPolytope.md)
