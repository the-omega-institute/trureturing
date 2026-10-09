# Two-independence and upper two-star formation differ

## Abstract

A bipartite graph on ten vertices has a minimal two-star-forming set of size six, but every two-independent set has size at most five.

Let G be a finite simple graph on V, with decidable adjacency. Write d(G,S,v) for the number of neighbours of v in S. All sets below are finite vertex sets. The definitions are those of Rafik Sahbi, Upper k-Star-Forming Sets, k-Independence, and Upper Domination, arXiv:2610.03785v2, Definition 2.1 and Conjecture 4.2.

**Definition 1.1 (Selected induced degree is less than k).**

$$\operatorname{IsKIndependent}\left(G, k, I\right) \Leftrightarrow \left(\forall v \in V,\; \operatorname{Member}\left(v, I\right) \Rightarrow \operatorname{d}\left(G, I, v\right) < k\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.IsKIndependent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each selected vertex has fewer than k selected neighbours. For k equal to two, the induced graph is a disjoint union of edges and isolated vertices.

**Definition 1.2 (Maximum k-independent cardinality).**

$$\operatorname{beta}\left(G, k\right) = \operatorname{supCard}\left(\{I \in \operatorname{powerset}\left(\operatorname{univ}\left(V\right)\right) \mid \operatorname{IsKIndependent}\left(G, k, I\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the maximum cardinality over the k-independent subsets of V. The finite supremum has value zero if the family is empty.

**Definition 1.3 (A star containing each outside vertex).**

$$\operatorname{IsStarForming}\left(G, k, S\right) \Leftrightarrow \left(\forall v \in V,\; \left(\neg \operatorname{Member}\left(v, S\right)\right) \Rightarrow \left(\exists c \in V,\; \exists L \in \operatorname{Finset}\left(V\right),\; \operatorname{card}\left(L\right) = k \land \left(\left(\neg \operatorname{Member}\left(c, L\right)\right) \land \left(\operatorname{Subset}\left(\operatorname{insert}\left(c, L\right), \operatorname{insert}\left(v, S\right)\right) \land \left(\left(\forall ell \in V,\; \operatorname{Member}\left(ell, L\right) \Rightarrow \operatorname{Adj}\left(G, c, ell\right)\right) \land \operatorname{Member}\left(v, \operatorname{insert}\left(c, L\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.IsStarForming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every vertex outside S, the graph on S together with that vertex contains a star with k leaves containing the vertex. The centre is distinct from all leaves. Extra edges between leaves are allowed: the star is a subgraph, with no induced-subgraph requirement.

**Definition 1.4 (Inclusion-minimal star formation).**

$$\operatorname{IsMinimalStarForming}\left(G, k, S\right) \Leftrightarrow \left(\operatorname{IsStarForming}\left(G, k, S\right) \land \left(\forall T \in \operatorname{Finset}\left(V\right),\; \operatorname{ProperSubset}\left(T, S\right) \Rightarrow \left(\neg \operatorname{IsStarForming}\left(G, k, T\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.IsMinimalStarForming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set is star-forming and no proper subset is star-forming. This is inclusion-minimality rather than minimum cardinality.

**Definition 1.5 (Upper k-star-forming number).**

$$\operatorname{SF}\left(G, k\right) = \operatorname{supCard}\left(\{S \in \operatorname{powerset}\left(\operatorname{univ}\left(V\right)\right) \mid \operatorname{IsMinimalStarForming}\left(G, k, S\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.SF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the maximum cardinality among all inclusion-minimal k-star-forming sets. The finite supremum has value zero if the family is empty.

**Definition 1.6 (Two local alternatives).**

$$\operatorname{LocalTwo}\left(G, S\right) \Leftrightarrow \left(\forall v \in V,\; \left(\neg \operatorname{Member}\left(v, S\right)\right) \Rightarrow \left(2 \le \operatorname{d}\left(G, S, v\right) \lor \left(\exists u \in V,\; \operatorname{Member}\left(u, S\right) \land \left(\operatorname{Adj}\left(G, v, u\right) \land 1 \le \operatorname{d}\left(G, S, u\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.LocalTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every outside vertex either has two neighbours in S, or has a neighbour in S that itself has a neighbour in S. In the second alternative this further neighbour cannot be the outside vertex.

**Theorem 1.7 (The local criterion equals the star definition).**

$$\forall V \in Type,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall S \in \operatorname{Finset}\left(V\right),\; \operatorname{IsStarForming}\left(G, 2, S\right) \Leftrightarrow \operatorname{LocalTwo}\left(G, S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.starForming_two_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a two-leaf star, the outside vertex is either the centre, giving two neighbours in S, or a leaf, giving a centre and another leaf in S. Conversely, two selected neighbours give a star centred at the outside vertex; a selected neighbour with its own selected neighbour gives a star centred at that selected neighbour. The argument works on any vertex type with decidable equality and adjacency.

**Definition 1.8 (Equality on all bipartite finite graphs).**

$$claim \Leftrightarrow \left(\forall n \in Nat,\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{Colorable}\left(G, 2\right) \Rightarrow \operatorname{beta}\left(G, 2\right) = \operatorname{SF}\left(G, 2\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjecture 4.2 asserts equality for every bipartite finite graph. Graphs on Fin n cover every finite simple graph up to isomorphism. Bipartiteness is expressed by a proper colouring with two colours.

**Theorem 1.9 (The equality is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sahbi-2026-star-forming-bipartite-refutation` (refuted) by `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sahbi-2026-star-forming-bipartite-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Use vertices 0 through 9, with sides 0 through 4 and 5 through 9. The neighbourhoods on the first side are {5,6,9}, {5,6,8}, {8,9}, {6,7,8,9}, and {5,7,8,9}, respectively. Colour by side. The set {0,1,2,5,6,7} satisfies the local criterion, while each of its 63 proper subsets fails it. It is therefore minimal two-star-forming, so SF is at least six. Each of the 210 six-element vertex sets contains a vertex with at least two selected neighbours. Any larger two-independent set would contain a two-independent six-element subset, since deletion cannot increase selected degrees. Thus beta is at most five and the asserted equality fails.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.IsKIndependent`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.IsMinimalStarForming`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.IsStarForming`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.LocalTwo`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.SF`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.starForming_two_iff`
