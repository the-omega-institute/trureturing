# A thin coordinate half has fifteen vertices and exact incidence

## Abstract

A nonempty Huang-balanced induced cubic Q9 support with a coordinate-zero half of size at most sixteen has size54 and that half is a fifteen-vertex K3,3 subdivision.

The graph, vertex set and Huang balance in this theorem all refer to the same actual subset of Q9. The coordinateSlice is the existing coordinate-zero filter, with its induced cube adjacency. No replacement abstract graph or supplied labels are assumed. This is a structural step toward Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2). The original f₂(Q₉) problem remains open.

**Theorem 1.1 (thin_coordinate_slice).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ThinCoordinateSlice.thin_coordinate_slice`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ThinCoordinateSlice.thin_coordinate_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every C : Finset (Q 9), if C is nonempty, its actual induced hypercube graph is regular of degree three and BalancedCriticalSpectrum.IsBalanced C holds, then for every b : Bool with (coordinateSlice C b).card ≤ 16, C.card=54, (coordinateSlice C b).card=15, and the actual induced slice graph satisfies FifteenSliceStructure.IsK33Subdivision. In particular its six degree-three vertices and nine degree-two vertices have the exact incidence of the once-subdivision of K3,3.

Put q=directionEdges C 0 and s=|coordinateSlice C b|. The proved BalancedCubeFiftyFourLowerBound.result gives |C|≥54, while the directional identity gives 6q=|C|. The actual slice lemmas give degrees two or three, exactly q degree-two vertices, independent degree-two vertices, actual parity bipartiteness and girth at least eight. Counting their incident edges gives 2q≤3(s-q), so 5q≤3s≤48. Consequently q=9 and |C|=54. The degree sum 3s-q is twice the number of actual slice edges. Together with 15≤s≤16 this forces s=15. The abstract structural theorem is then applied to this same induced slice and its actual parity sides.

The conclusion does not classify the cubical embedding of the slice, identify the remaining 39 vertices with a particular Gray54 support, or establish uniqueness under cube automorphisms. Embedding rigidity, signing gauge transport and the reconstruction of the other coordinate half remain separate mathematical obligations. No assertion is made that arbitrary balanced components have size 54 or possess a coordinate half of size at most 16.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ThinCoordinateSlice.thin_coordinate_slice`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound](BalancedCubeFiftyFourLowerBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure](FifteenSliceStructure.md)
