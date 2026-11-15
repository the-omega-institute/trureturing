# Cardinality and actual neighbors of the grid-wedge support

## Abstract

The two-layer block support has an exact uniform cardinality and inherits regular degree from actual Boolean cube adjacency.

Fix a natural d at least two and partition the d squared Boolean coordinates into d rows. The upper layer has one marked double row and singleton entries elsewhere. The lower layer either has a marked double row, one empty row, and all other rows singleton, or is a transversal containing exactly one of the two marked coordinates. The graph is the induced subgraph on this explicit support, with no regularity assumption. The external motivation is Hong–Wu–Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2: https://arxiv.org/html/2610.09483v1#Thmproblem2 . This support/count construction is repository-derived; it does not resolve that problem. The companion complete construction records the related literature and the limitations of the bounded search.

**Theorem 1.1 (Exactly d actual neighbors at every selected vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.component_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.component_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least two, the induced graph is regular of degree d. A bijection identifies the full actual neighbor set with the coordinates whose flip remains in the support. Lower double vertices can only fill their empty row, in d ways. Transversals have d-1 additions in their occupied marked row and one addition of the other marked coordinate. An upper vertex has exactly one legal deletion in each row: in its double row precisely one of the two deletions gives a transversal containing exactly one mark. All other coordinates are excluded by the row patterns and the two permitted total weights.

**Theorem 1.2 (The exact number of vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.card_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.card_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d at least two, the support has 4*(d-1)*d^(d-1) vertices. The upper layer is in bijection with two choices of double row, d-1 choices of its different column, and d choices in each of the remaining d-1 rows. Thus its size is 2*(d-1)*d^(d-1). Every edge joins the upper weight d+1 to the lower weight d. Equality of the two degree sums and d>0 give equal layer sizes, hence the claimed total. These are the cardinality and degree inputs to the connected balanced construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.card_support`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/GridWedgeSupport.component_regular`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube](../Hypercube.md)
