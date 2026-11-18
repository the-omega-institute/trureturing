# Sixteen Cycle Exclusion

## Abstract

Sixteen Cycle Exclusion

Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), ask whether f2(Q9) is three or four. The external f2(Q9) problem remains open. This result settles only the C16 high-cycle structural branch.

The claim quantifies over a finite simple graph with a bipartition, degrees two or three, independent degree-two vertices, girth at least eight, and an injectively labelled induced C16 containing every degree-three vertex. The proof derives the unique low partner at each cycle vertex from the actual degree conditions and high-cycle coverage. Girth and the existing short-path exclusions force each partner displacement to be 6, 8, or 10. The resulting involution and adjacent-image separation are discharged by a finite 3^8 enumeration checked by the Lean kernel with decide +kernel. No trusted SAT solver or certificate-style matching premise is used.

**Definition 1.1 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exist a finite bipartite simple graph G, finite side sets L and R, and an induced injective C16 labelling c whose image is exactly the degree-three vertices, while every graph vertex has degree two or three, degree-two vertices are independent, and the girth is at least eight.

**Theorem 1.2 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem has literally type Not claim. It excludes the C16 high-cycle branch by deriving the low matching from the graph premises and then applying the kernel-checked finite displacement contradiction; it does not settle the external f2(Q9) problem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion.result`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceLabels](AsymmetricSliceLabels.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting](GirthSliceCounting.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPartners](SymmetricLowPartners.md)
