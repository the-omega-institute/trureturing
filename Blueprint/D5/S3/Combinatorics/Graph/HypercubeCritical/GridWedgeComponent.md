# Grid-wedge components in Boolean cubes

## Abstract

A uniform block construction gives connected balanced regular induced subgraphs of square-dimensional Boolean cubes, with an explicit exact size.

Hong, Wu and Xia ask whether 258 vertices of the nine-dimensional Boolean cube can induce maximum degree three. The construction here supplies critical components for investigation of that question. The case d=3 has 72 vertices; it is not a 258-vertex witness or an exclusion of every such witness. No resolution or worldwide priority claim is made.

**Definition 1.1 (An explicit support in the actual cube).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.support`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.support` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhen-Mu Hong, Zi-Yi Wu, Zheng-Jiang Xia (2026). *Graph Sensitivity of Cartesian Products with Matched Bridges*. DOI: [10.48550/arXiv.2610.09483](https://doi.org/10.48550/arXiv.2610.09483). URL: <https://arxiv.org/html/2610.09483v1>.

*Commentary.*

For every natural d at least two, arrange the d squared coordinates into d rows of d columns. Mark column zero in rows zero and one. An upper vertex has a double marked row containing its marked coordinate and one different column; all other rows are singletons. A lower vertex either has such a double row, exactly one other empty row, and singleton entries in all remaining rows, or is a transversal containing exactly one of the two marked coordinates. Every vertex is a literal Boolean function on Fin(d*d); the row conditions determine membership.

**Definition 1.2 (Inherited hypercube adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.componentGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.componentGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zhen-Mu Hong, Zi-Yi Wu, Zheng-Jiang Xia (2026). *Graph Sensitivity of Cartesian Products with Matched Bridges*. DOI: [10.48550/arXiv.2610.09483](https://doi.org/10.48550/arXiv.2610.09483). URL: <https://arxiv.org/html/2610.09483v1>.

*Commentary.*

The graph is the induced subgraph of the existing repository hypercube on this support. Two selected vertices are adjacent precisely when their actual Boolean functions disagree in exactly one coordinate. Regularity and connectedness are conclusions, not assumptions in the definition.

**Theorem 1.3 (The uniform connected regular construction).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeComponent.grid_wedge_component`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeComponent.grid_wedge_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zhen-Mu Hong, Zi-Yi Wu, Zheng-Jiang Xia (2026). *Graph Sensitivity of Cartesian Products with Matched Bridges*. DOI: [10.48550/arXiv.2610.09483](https://doi.org/10.48550/arXiv.2610.09483). URL: <https://arxiv.org/html/2610.09483v1>.

*Commentary.*

The result quantifies over every d at least two. The support has 4*(d-1)*d^(d-1) vertices and its induced cube graph is connected and regular of degree d. Its switching balance uses the explicitly defined signing whose edge in direction k is minus one to the number of occupied coordinates before k. This signing convention is stated explicitly; it is not silently identified with the different Boolean basis convention in Archive.Sensitivity.

The upper layer is parametrized injectively by a choice of marked row, a different column in that row, and one column in every other row. This gives 2*(d-1)*d^(d-1) upper vertices. Each lower double vertex has d neighbors obtained by filling its empty row. A lower transversal has d-1 additions in its marked row and one addition of the other marked coordinate. Each upper vertex has d+1 possible deletions, of which exactly one produces a forbidden transversal. These are classifications of actual cube flips.

The equal degree sums on the two parts give equal layer sizes. Connectivity follows by changing singleton rows through shared lower neighbors, then using a transversal to connect different double columns and the two marked-row classes. Every lower vertex has a positive number of upper neighbors. The sign calculation follows the same classified flips.

The first three sizes are eight vertices at d=2, 72 at d=3, and 768 at d=4. The nine-cube sensitivity question requires 258 vertices of maximum degree at most three, so it remains separate from this construction. General spectral equality and switching-balance mechanisms are prior work of Laplante, Naserasr, Sunny and Wang; exterior-algebra and Clifford descriptions appear in Karasev and Mathews. The candidate new content here is the explicit block support, its exact count and its connected induced graph, subject to the literature limitations recorded in the source note.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeComponent.grid_wedge_component`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.componentGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.support`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport](GridWedgeSupport.md)
