# The Koch-Narayan bipartite edge bound is false

## Abstract

A graph with fourteen vertices, twenty-eight edges and a unique minimum dominating set of size four exceeds the printed bound twenty-six.

**Definition 1.1 (Exact ceiling).**

$$\operatorname{halfCeil}\left(k\right) = \operatorname{ceil}\left(\frac{k}{2}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.halfCeil` (`✓ std3`).

*Citation.* Garrison Koch; Darren Narayan (2025). *Maximal bipartite graphs with a unique minimum dominating set*. DOI: [10.48550/arXiv.2511.01719](https://doi.org/10.48550/arXiv.2511.01719). URL: <https://arxiv.org/abs/2511.01719v1>.

*Commentary.*

halfCeil(k) is the integer ceiling of the rational number k/2. Division is exact before rounding.

**Definition 1.2 (Exact floor).**

$$\operatorname{halfFloor}\left(k\right) = \left\lfloor\frac{k}{2}\right\rfloor$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.halfFloor` (`✓ std3`).

*Citation.* Garrison Koch; Darren Narayan (2025). *Maximal bipartite graphs with a unique minimum dominating set*. DOI: [10.48550/arXiv.2511.01719](https://doi.org/10.48550/arXiv.2511.01719). URL: <https://arxiv.org/abs/2511.01719v1>.

*Commentary.*

halfFloor(k) is the integer floor of the rational number k/2.

**Definition 1.3 (The printed positive part).**

$$\operatorname{phi}\left(n, gamma\right) = \operatorname{max}\left(0, n - 3 \cdot gamma - 2 \cdot \operatorname{halfCeil}\left(gamma\right) - \operatorname{halfFloor}\left(gamma\right) + 1\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.phi` (`✓ std3`).

*Citation.* Garrison Koch; Darren Narayan (2025). *Maximal bipartite graphs with a unique minimum dominating set*. DOI: [10.48550/arXiv.2511.01719](https://doi.org/10.48550/arXiv.2511.01719). URL: <https://arxiv.org/abs/2511.01719v1>.

*Commentary.*

With a=ceil(gamma/2) and b=floor(gamma/2), Phi=max(0,n-3gamma-2a-b+1). Every subtraction is in the integers. In particular Phi(14,4)=0; left-associated truncated natural subtraction would change the formula.

**Definition 1.4 (The exact printed edge bound).**

$$\operatorname{bound}\left(n, gamma\right) = 2 \cdot gamma + 2 \cdot \operatorname{halfCeil}\left(gamma\right) \cdot \operatorname{halfFloor}\left(gamma\right) + \operatorname{min}\left(n - 3 \cdot gamma, 2 \cdot \operatorname{halfCeil}\left(gamma\right) - \operatorname{halfFloor}\left(gamma\right) + 1\right) \cdot \left(2 \cdot \operatorname{halfCeil}\left(gamma\right) + 1\right) + \sum_{i = 1}^{\operatorname{phi}\left(n, gamma\right)}{2 \cdot \operatorname{halfCeil}\left(gamma\right) + 1 + \operatorname{ceil}\left(\frac{i}{2}\right)}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.bound` (`✓ std3`).

*Citation.* Garrison Koch; Darren Narayan (2025). *Maximal bipartite graphs with a unique minimum dominating set*. DOI: [10.48550/arXiv.2511.01719](https://doi.org/10.48550/arXiv.2511.01719). URL: <https://arxiv.org/abs/2511.01719v1>.

*Commentary.*

The bound is 2gamma+2ab+min(n-3gamma,2a-b+1)(2a+1), plus the sum of (2a+1)+ceil(i/2) over the inclusive integer interval 1 through Phi. An empty interval contributes zero. Both the minimum and the signed arithmetic are exactly those printed in Conjecture 1.

**Definition 1.5 (Conjecture 1 on its whole domain).**

$$claim \Leftrightarrow \left(\forall V \in Type,\; \forall finite \in \operatorname{Fintype}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \left(\operatorname{IsBipartite}\left(G\right) \land \left(\left(\forall v \in V,\; \neg \operatorname{IsIsolated}\left(G, v\right)\right) \land \left(\left(\exists D \in \operatorname{Set}\left(V\right),\; \left(\operatorname{IsDominating}\left(G, D\right) \land \operatorname{ncard}\left(D\right) = \operatorname{dominationNumber}\left(G\right)\right) \land \left(\forall S \in \operatorname{Set}\left(V\right),\; \left(\operatorname{IsDominating}\left(G, S\right) \land \operatorname{ncard}\left(S\right) = \operatorname{dominationNumber}\left(G\right)\right) \Rightarrow S = D\right)\right) \land \left(2 \le \operatorname{dominationNumber}\left(G\right) \land 3 \cdot \operatorname{dominationNumber}\left(G\right) \le \operatorname{card}\left(V\right)\right)\right)\right)\right) \Rightarrow \operatorname{card}\left(\operatorname{edgeFinset}\left(G\right)\right) \le \operatorname{bound}\left(\operatorname{card}\left(V\right), \operatorname{dominationNumber}\left(G\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.claim` (`✓ std3`).

*Citation.* Garrison Koch; Darren Narayan (2025). *Maximal bipartite graphs with a unique minimum dominating set*. DOI: [10.48550/arXiv.2511.01719](https://doi.org/10.48550/arXiv.2511.01719). URL: <https://arxiv.org/abs/2511.01719v1>.

*Commentary.*

Koch and Narayan, arXiv:2511.01719v1, Conjecture 1, assert this bound for every finite simple bipartite graph without isolated vertices, with a unique minimum dominating set, gamma at least two and n at least three gamma. The vertex type is arbitrary; n is its Fintype cardinality. The graph is an actual SimpleGraph and its size is edgeFinset.card, counting unordered edges once. IsDominating, IsNDominatingSet and dominationNumber are the existing native definitions. Uniqueness quantifies over every Set V attaining dominationNumber. On a finite type, the proof identifies attainment with minimum cardinality among all dominating sets using native minimum attainment, the native domination upper bound and the Set/Finset membership and cardinality equalities. There is no connectedness, minimum-degree-two, balanced-center or constructed-family assumption.

**Definition 1.6 (The oriented edges).**

$$\operatorname{forward}\left(u, v\right) \Leftrightarrow \left(\left(u = 0 \land v \in \left\{10, 11, 12, 13\right\}\right) \lor \left(\left(u \in \left\{1, 2\right\} \land v = 7\right) \lor \left(\left(u \in \left\{3, 4\right\} \land v = 8\right) \lor \left(\left(u \in \left\{5, 6\right\} \land v = 9\right) \lor \left(\left(1 \le u \land u \le 6\right) \land v \in \left\{10, 12, 13\right\}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.forward` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrison Koch; Darren Narayan (2025). *Maximal bipartite graphs with a unique minimum dominating set*. DOI: [10.48550/arXiv.2511.01719](https://doi.org/10.48550/arXiv.2511.01719). URL: <https://arxiv.org/abs/2511.01719v1>.

*Commentary.*

The parts are {0,...,6} and {7,...,13}. Join 0 to 10,11,12,13; join 7 to 1,2, join 8 to 3,4 and join 9 to 5,6; join each of 1,...,6 to each of 10,12,13. These disjoint families have four, six and eighteen edges. forward orients each edge from the first part to the second.

**Definition 1.7 (The fourteen-vertex graph).**

$$\operatorname{Adj}\left(graph, u, v\right) \Leftrightarrow \left(\operatorname{forward}\left(u, v\right) \lor \operatorname{forward}\left(v, u\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.graph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrison Koch; Darren Narayan (2025). *Maximal bipartite graphs with a unique minimum dominating set*. DOI: [10.48550/arXiv.2511.01719](https://doi.org/10.48550/arXiv.2511.01719). URL: <https://arxiv.org/abs/2511.01719v1>.

*Commentary.*

Adjacency is forward in either direction. The disjoint parts exclude loops and reversal gives symmetry. Every edge crosses the parts, every vertex has a neighbor, and the actual edgeFinset has cardinality twenty-eight.

**Definition 1.8 (The unique minimum dominating set).**

$$centers = \left\{0, 7, 8, 9\right\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.centers` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Garrison Koch; Darren Narayan (2025). *Maximal bipartite graphs with a unique minimum dominating set*. DOI: [10.48550/arXiv.2511.01719](https://doi.org/10.48550/arXiv.2511.01719). URL: <https://arxiv.org/abs/2511.01719v1>.

*Commentary.*

The centers are {0,7,8,9}. Their closed neighborhoods are {0,10,11,12,13}, {7,1,2}, {8,3,4} and {9,5,6}. They partition the graph. Any dominating set meets every block to dominate its center, so the image under the block map has cardinality four and the set has at least four members. The centers themselves dominate, and native attainment therefore gives dominationNumber=4.

**Theorem 1.9 (The whole conjecture is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/koch-narayan-2025-bipartite-unique-domination-edge-bound` (refuted) by `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"koch-narayan-2025-bipartite-unique-domination-edge-bound","declaration_gid":"D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Garrison Koch; Darren Narayan (2025). *Maximal bipartite graphs with a unique minimum dominating set*. DOI: [10.48550/arXiv.2511.01719](https://doi.org/10.48550/arXiv.2511.01719). URL: <https://arxiv.org/abs/2511.01719v1>.

*Commentary.*

A dominating set of size four has exactly one member in each block: equality of the block-image cardinality makes the block map injective on the set. Leaf 11 forces the first choice into {0,11}, so hubs 10,12,13 are absent. If a noncenter is chosen in any other block, its partner has no selected neighbor; hence 7,8,9 must all be chosen and 1,...,6 are absent. The choice 11 would leave 10 undominated, forcing 0 as well. Thus every minimum set equals the centers. Finite Set/Finset conversion preserves domination, membership, cardinality and equality, giving uniqueness over all sets. Substituting n=14, gamma=4 gives a=b=2, Phi=0 and bound 8+8+min(2,3)*5=26, contradicting 28 edges. The printed Phi differs from the residual count suggested by construction Case 3, max(0,n-3gamma-2a+b-1); both are zero here, and Case 2 also gives 26. This proves no true extremal formula and settles neither an unspecified corrected conjecture nor the unrestricted predecessor problem. The elementary private-neighbor mechanism is also used in the source; the imported domination port retains its formal-conjectures Apache-2.0 attribution.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.centers`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.forward`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.graph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.halfCeil`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.halfFloor`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.phi`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/KochNarayanRefutation.result`
- Dependency: [D5/S3/ConceptDynamics/GraphColoring/GraphCoverDomination](../../../ConceptDynamics/GraphColoring/GraphCoverDomination.md)
