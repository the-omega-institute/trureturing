# Even direction links of separated cubic cube supports

## Abstract

Even direction links of separated cubic cube supports

**Theorem 1.1 (Huang cancellation makes every direction-link degree even).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.even_card_exteriorLinkNeighbors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.even_card_exteriorLinkNeighbors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a cube vertex x with no neighbor in C, form a graph on directions whose first flip stays outside the separated partner D. Two directions are joined if their two flips land in C. The coordinate flips commute, and separation ensures that every two-flip contact uses exterior directions. The link degree at a direction counts the C-neighbors of the first-flip vertex, which is even by Huang exterior cancellation.

**Theorem 1.2 (Three exterior directions give an empty link or a triangle).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.exteriorLink_empty_or_complete_of_card_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.exteriorLink_empty_or_complete_of_card_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With three available directions a nonempty row has degree two. Symmetry forces the other two rows to have degree two. The triangle means each available direction leads to a vertex with two C-neighbors.

**Theorem 1.3 (A high exterior neighbor rules out the triangle).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.pairFlips_not_mem_of_card_three_of_highLeaf`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.pairFlips_not_mem_of_card_three_of_highLeaf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If one first-flip vertex is outside D and all eight transverse second flips land in D, that direction has no link edges. With three exterior directions the entire link is empty, so every pair flip stays outside C.

**Theorem 1.4 (A two-flip contact forces at least three contact vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.three_le_card_pairFlipContacts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.three_le_card_pairFlipContacts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions of one contact have positive even link degree. A second edge at each end gives three edges that flip distinct unordered pairs and reach three different points of C.

For Hong, Wu and Xia's open Problem 2, apply the lemma at a vertex of D to bound how many D-vertices can be within distance two of C for a fixed contact count. This bounds the radius-two neighborhood of each parity class in the separated order-72 and order-186 equality analysis. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.even_card_exteriorLinkNeighbors`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.exteriorLink_empty_or_complete_of_card_three`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.pairFlips_not_mem_of_card_three_of_highLeaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureExteriorLink.three_le_card_pairFlipContacts`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
