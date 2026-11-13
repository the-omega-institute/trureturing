# Common-neighborhood energy of the noncentral commuting graph

## Abstract

The unrestricted finite nonabelian commuting-graph CN energy comparison.

**Definition 1.1 (Individual noncentral vertices).**

$$\forall G \in \operatorname{Type},\; [\operatorname{Group}\left(G\right)]\operatorname{Vertex}\left(G\right) = \{x:G\mid\neg x \in \operatorname{Subgroup}.\operatorname{center}\left(G\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.Vertex` (`✓ std3`).

*Citation.* Rajat Kanti Nath; Walaa N. T. Fasfous; Kinkar Chandra Das; Yilun Shang (2021). *Common Neighborhood Energy of Commuting Graphs of Finite Groups*. DOI: [10.3390/sym13091651](https://doi.org/10.3390/sym13091651). URL: <https://doi.org/10.3390/sym13091651>.

*Commentary.*

For every group G, Vertex(G) is the subtype of elements outside its center. Vertices are individual elements. No quotient by conjugacy is taken.

**Definition 1.2 (The exact simple graph).**

$$\forall G \in \operatorname{Type},\; [\operatorname{Group}\left(G\right)]\forall x \in \operatorname{Vertex}\left(G\right),\; \forall y \in \operatorname{Vertex}\left(G\right),\; \operatorname{SimpleGraph}.\operatorname{Adj}\left((\operatorname{commutingGraph}\left(G\right):\operatorname{SimpleGraph}\left(\operatorname{Vertex}\left(G\right)\right)), x, y\right) \Leftrightarrow \left(x \ne y \land \operatorname{Subtype}.\operatorname{val}\left(x\right) \cdot \operatorname{Subtype}.\operatorname{val}\left(y\right) = \operatorname{Subtype}.\operatorname{val}\left(y\right) \cdot \operatorname{Subtype}.\operatorname{val}\left(x\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.commutingGraph` (`✓ std3`).

*Citation.* Rajat Kanti Nath; Walaa N. T. Fasfous; Kinkar Chandra Das; Yilun Shang (2021). *Common Neighborhood Energy of Commuting Graphs of Finite Groups*. DOI: [10.3390/sym13091651](https://doi.org/10.3390/sym13091651). URL: <https://doi.org/10.3390/sym13091651>.

*Commentary.*

The simple graph has the preceding vertex type; adjacency requires distinctness and equality of the two products in G. Its symmetry and absence of loops are part of the Lean definition. The value map is the canonical subtype inclusion into G.

**Theorem 1.3 (The full finite nonabelian bound).**

$$\forall G \in \operatorname{Type},\; [\operatorname{Group}\left(G\right)][\operatorname{Fintype}\left(G\right)]\left(\exists a \in G,\; \exists b \in G,\; a \cdot b \ne b \cdot a\right) \Rightarrow \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{graphEnergy}\left(\operatorname{commutingGraph}\left(G\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{MatrixKind}.\operatorname{commonNeighbour}\right) \le 2 \cdot \left((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(G\right)\right):\mathbb{R}) - 1\right) \cdot \left((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(G\right)\right):\mathbb{R}) - 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/nath2021-commuting-cn-conjecture2` (proved) by `D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nath2021-commuting-cn-conjecture2","declaration_gid":"D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Rajat Kanti Nath; Walaa N. T. Fasfous; Kinkar Chandra Das; Yilun Shang (2021). *Common Neighborhood Energy of Commuting Graphs of Finite Groups*. DOI: [10.3390/sym13091651](https://doi.org/10.3390/sym13091651). URL: <https://doi.org/10.3390/sym13091651>.

*Acknowledgement.* Firdous Ee Jannat; Rajat Kanti Nath; Kinkar Chandra Das (2024). *Common neighborhood energies and their relations with Zagreb index*. DOI: [10.48550/arXiv.2402.15416](https://doi.org/10.48550/arXiv.2402.15416). URL: <https://arxiv.org/abs/2402.15416v1>.

*Commentary.*

For every group G with finite underlying set and a pair a,b whose products differ, the common-neighborhood energy of commutingGraph(G) is at most the displayed complete-graph benchmark. The cardinality is explicitly cast into the reals before subtracting one or two. No AC, quotient, order, regularity, genus or connectivity hypothesis is present.

For a finite simple graph g, commonNeighbourMatrix(g) has diagonal zero and off-diagonal common-neighbor cardinalities. The real symmetric matrix has a complete real eigenvalue multiset, graphSpectrum(g,commonNeighbour), with algebraic multiplicity. Its energy graphEnergy(g,commonNeighbour) sums the absolute values of this multiset, with zero centering. Here g is commutingGraph(G).

Write A for adjacency, D for the degree diagonal, N for the group order, z for the center order and n=N-z. Entrywise counting gives C=A squared minus D. The general energy bound is twice the sum of degrees. In an orthogonal eigenbasis of C, the absolute difference of the two nonnegative diagonal quadratic terms is at most their sum. Summing gives the sum of their traces. This argument requires no simultaneous diagonalization of A and D.

For each noncentral x, its centralizer K is proper. The subgroup index is at least two, so twice its order is at most N. The center, x, and all its graph neighbors are pairwise disjoint inside K; their cardinalities give degree(x)+z+1 at most the order of K. Hence twice degree(x) is at most n-z-2. Summation gives energy at most n(n-z-2). The difference from the target is (n-2) squared plus nz, which is nonnegative. All subtractions in this estimate occur in the integers or reals after finite cardinality relations have been justified.

The complete-graph benchmark applies for n at least two. A noncentral centralizer contains the center and x, so the same index bound gives n at least z+2. The center contains the identity, whence z is at least one and n is at least three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.commutingGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.result`
- Dependency: [D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation](../SubgroupGenerating/CyclicExtensionRefutation.md)
