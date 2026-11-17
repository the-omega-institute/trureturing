# The exact incidence structure of a fifteen-vertex slice

## Abstract

A bipartite fifteen-vertex graph of girth at least eight, degrees two or three, and nine independent degree-two vertices is a once-subdivided K3,3.

This finite graph characterization supplies a structural step in the Q9 problem of Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2). The classification below is repository-derived; no literature priority is asserted. It concerns abstract slice incidence and does not classify cube embeddings or whole balanced supports. The original f₂(Q₉) problem remains open.

**Definition 1.1 (IsK33Subdivision).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure.IsK33Subdivision`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure.IsK33Subdivision` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any finite decidable vertex type V and simple graph G on V, IsK33Subdivision G asserts the existence of a bipartition L,R covering every vertex, with |L|=6 and |R|=9, degree three on L and degree two on R. The subtype L is partitioned into disjoint three-element sets A,B. Every pair a in A, b in B has exactly one common neighbor m in R. Conversely, each m in R has neighborFinset exactly {a.val,b.val} for some such pair. These are statements about the actual adjacency relation G. They specify all vertices and all edges, including absence of additional edges; no incidence certificate is an input.

**Theorem 1.2 (fifteen_vertex_subdivision).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure.fifteen_vertex_subdivision`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure.fifteen_vertex_subdivision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite decidable V, simple graph G on V and finite bipartition L,R covering V, assume every degree is two or three, adjacent degree-two vertices are forbidden, 8 ≤ G.egirth, |V|=15 and exactly nine vertices have degree two. Then IsK33Subdivision G. Connectedness, labels, a suppression graph and a cube embedding are not hypotheses.

Write a=|L|, b=|R| and p,r for the numbers of degree-two vertices in the two sides. Degree balance gives a+b=15, p+r=9 and 3a-p=3b-r. Up to exchanging sides there are two possibilities: (a,b;p,r)=(6,9;0,9) or (7,8;3,6). In the second case R has exactly two degree-three vertices. Every degree-two vertex of L has those two vertices as its whole neighbor set. Two distinct such vertices already force a four-cycle; the existing short-path uniqueness lemma rules this out. Thus all nine middle vertices lie on one side and all six branch vertices on the other.

Compress each actual degree-two vertex to the edge between its two distinct branch neighbors. Girth forbids two different middles on the same compressed edge, so the three actual neighbors of each branch vertex give three distinct compressed neighbors. A compressed triangle would give distinct actual paths of length three with common endpoints, again contradicting girth. The resulting simple graph is therefore cubic and triangle-free on six vertices. The three neighbors B of any root are independent. Every vertex of B must use all three vertices of the complement A as neighbors, giving precisely K3,3. Transferring this exact adjacency table back through compression yields unique middles for every cross pair and the complete two-neighbor table for every middle.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure.IsK33Subdivision`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure.fifteen_vertex_subdivision`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound](BalancedCubeLowerBound.md)
