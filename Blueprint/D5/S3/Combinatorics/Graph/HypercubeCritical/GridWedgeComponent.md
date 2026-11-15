# Grid-wedge components in Boolean cubes

## Abstract

A uniform block construction gives connected balanced regular induced subgraphs of square-dimensional Boolean cubes, with an explicit exact size.

Hong, Wu and Xia ask whether 258 vertices of the nine-dimensional Boolean cube can induce maximum degree three. The construction here supplies critical components for investigation of that question. The case d=3 has 72 vertices; it is not a 258-vertex witness or an exclusion of every such witness. No resolution or worldwide priority claim is made.

The external anchor is Zhen-Mu Hong, Zi-Yi Wu and Zheng-Jiang Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, 7 October 2026, DOI 10.48550/arXiv.2610.09483. Section 7, Problem 2 asks: Determine whether f₂(Q₉)=3 or 4. Exact primary locator: https://arxiv.org/html/2610.09483v1#Thmproblem2 . The source defines f_t(G) as the minimum maximum induced degree on alpha(G)+t vertices. Since alpha(Q₉)=256, the target requires 258 vertices of maximum degree at most three, or a complete exclusion. The versioned source was read on 15 November 2026. This construction is a repository derivation motivated by that source, not its theorem.

Related prior work: Laplante, Naserasr, Sunny and Wang, Sensitivity conjecture and signed hypercubes, https://hal.science/hal-04080411/document , commentary after Lemma 4.1 (PDF page 9, printed page 7) and Theorem 6.2 (PDF page 26, printed page 24), already supply general equality regularity and switching mechanisms. The final journal DOI is 10.1145/3777401; that full text was not read. Karasev, https://arxiv.org/abs/1907.11175v2 , Sections 1.2–1.3, and Mathews, https://arxiv.org/abs/1907.12357v2 , Sections 2.2–2.3, give exterior-algebra and Clifford formulations. Those methods and general equality mechanisms are not claimed as new.

The source https://arxiv.org/abs/2312.15336v1 , Section 1 and Construction 1, identifies the standard Gray graph as the Levi graph of the 27-point, 27-line three-dimensional grid. Our 72-point case differs from that 54-point graph; this does not rule out every generalized Gray construction. Bouwer's 1972 original paper was not read. On 15 November 2026 the official anchor abstract page listed only v1, and a bounded Semantic Scholar lookup reported zero citations. This is not an exhaustive search for later work or evidence of worldwide priority. The exact block family was not found in the related texts read; the candidate new content is its explicit support, exact size and connectedness.

Signing conventions: here the exponent counts occupied earlier coordinates. Pinned Archive.Sensitivity instead counts unoccupied earlier coordinates. On direction k the signs differ by (-1)^k; the vertex potential (-1)^(sum of occupied coordinate indices) supplies diagonal switching. This is a mathematical convention correspondence; no Lean ambient matrix or gauge bridge is claimed by this combinatorial build.

**Definition 1.1 (An explicit support in the actual cube).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.support`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural d at least two, arrange the d squared coordinates into d rows of d columns. Mark column zero in rows zero and one. An upper vertex has a double marked row containing its marked coordinate and one different column; all other rows are singletons. A lower vertex either has such a double row, exactly one other empty row, and singleton entries in all remaining rows, or is a transversal containing exactly one of the two marked coordinates. Every vertex is a literal Boolean function on Fin(d*d); the row conditions determine membership.

**Definition 1.2 (Inherited hypercube adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.componentGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.componentGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph is the induced subgraph of the existing repository hypercube on this support. Two selected vertices are adjacent precisely when their actual Boolean functions disagree in exactly one coordinate. Regularity and connectedness are conclusions, not assumptions in the definition.

**Theorem 1.3 (The uniform connected regular construction).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeComponent.grid_wedge_component`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeComponent.grid_wedge_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The result quantifies over every d at least two. The support has 4*(d-1)*d^(d-1) vertices and its induced cube graph is connected and regular of degree d. Its switching balance uses the explicitly defined signing whose edge in direction k is minus one to the number of occupied coordinates before k. This signing convention is stated explicitly; it is not silently identified with the different Boolean basis convention in Archive.Sensitivity.

The upper layer is parametrized injectively by a choice of marked row, a different column in that row, and one column in every other row. This gives 2*(d-1)*d^(d-1) upper vertices. Each lower double vertex has d neighbors obtained by filling its empty row. A lower transversal has d-1 additions in its marked row and one addition of the other marked coordinate. Each upper vertex has d+1 possible deletions, of which exactly one produces a forbidden transversal. These are classifications of actual cube flips.

The equal degree sums on the two parts give equal layer sizes. Connectivity follows by changing singleton rows through shared lower neighbors, then using a transversal to connect different double columns and the two marked-row classes. Every lower vertex has a positive number of upper neighbors. The sign calculation follows the same classified flips.

The first three sizes are eight vertices at d=2, 72 at d=3, and 768 at d=4. The nine-cube sensitivity question requires 258 vertices of maximum degree at most three, so it remains separate from this construction. General spectral equality and switching-balance mechanisms are prior work of Laplante, Naserasr, Sunny and Wang; exterior-algebra and Clifford descriptions appear in Karasev and Mathews. The candidate new content here is the explicit block support, its exact count and its connected induced graph, subject to the literature limitations recorded above.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeComponent.grid_wedge_component`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.componentGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.support`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport](GridWedgeSupport.md)
