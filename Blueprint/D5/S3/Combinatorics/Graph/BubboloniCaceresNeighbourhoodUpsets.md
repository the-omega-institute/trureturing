# Upsets in neighbourhood convex geometries

## Abstract

Let V be any finite nonempty vertex set and G any simple undirected graph on V. Closed neighbourhoods include their centre. No connectivity, absence of universal vertices, or distinction of equal neighbourhoods is assumed.

**Definition 1.1 (Closed neighbourhood).**

Lean statement: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.closedNeighbourhood`

*Formalization.* `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.closedNeighbourhood` (`✓ std3`).

*Citation.* Daniela Bubboloni; José Cáceres (2026). *The neighbourhood convexity*. DOI: [10.48550/arXiv.2608.25912](https://doi.org/10.48550/arXiv.2608.25912). URL: <https://arxiv.org/html/2608.25912v1>.

*Commentary.*

B(x) consists of x and every vertex adjacent to x in G.

**Definition 1.2 (Neighbourhood polarity).**

Lean statement: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.common`

*Formalization.* `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.common` (`✓ std3`).

*Citation.* Daniela Bubboloni; José Cáceres (2026). *The neighbourhood convexity*. DOI: [10.48550/arXiv.2608.25912](https://doi.org/10.48550/arXiv.2608.25912). URL: <https://arxiv.org/html/2608.25912v1>.

*Commentary.*

N(X) is the intersection of B(x) over x in X. In particular N(empty) is V. Symmetry makes N antitone and gives X contained in N(N(X)) and N(N(N(X))) = N(X).

**Definition 1.3 (Neighbourhood-convex sets).**

Lean statement: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.convex`

*Formalization.* `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.convex` (`✓ std3`).

*Citation.* Daniela Bubboloni; José Cáceres (2026). *The neighbourhood convexity*. DOI: [10.48550/arXiv.2608.25912](https://doi.org/10.48550/arXiv.2608.25912). URL: <https://arxiv.org/html/2608.25912v1>.

*Commentary.*

The family C is the image of N together with the empty set: K belongs to C exactly when K is empty or K = N(Y) for some subset Y of V.

**Definition 1.4 (Empty-preserving hull).**

Lean statement: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.hull`

*Formalization.* `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.hull` (`✓ std3`).

*Citation.* Daniela Bubboloni; José Cáceres (2026). *The neighbourhood convexity*. DOI: [10.48550/arXiv.2608.25912](https://doi.org/10.48550/arXiv.2608.25912). URL: <https://arxiv.org/html/2608.25912v1>.

*Commentary.*

h(empty) is empty, and h(X) = N(N(X)) for every nonempty X. Double polarity at the empty set is not identified with this empty-preserving hull.

**Definition 1.5 (Extreme points by deletion).**

Lean statement: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.extremes`

*Formalization.* `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.extremes` (`✓ std3`).

*Citation.* Daniela Bubboloni; José Cáceres (2026). *The neighbourhood convexity*. DOI: [10.48550/arXiv.2608.25912](https://doi.org/10.48550/arXiv.2608.25912). URL: <https://arxiv.org/html/2608.25912v1>.

*Commentary.*

ex(K) consists of those x in K for which deleting x from K leaves a member of C.

**Theorem 1.6 (Every upset is neighbourhood-convex).**

$$\forall V \in FiniteNonemptySets,\; \forall G \in \operatorname{SimpleGraphs}\left(V\right),\; \forall U \in \operatorname{PowerSet}\left(V\right),\; (\forall K \in C,\; \operatorname{h}\left(\operatorname{ex}\left(K\right)\right) = K) \Rightarrow ((\forall x \in U,\; \forall y \in V,\; (\operatorname{B}\left(x\right) \subseteq \operatorname{B}\left(y\right)) \Rightarrow (y \in U)) \Rightarrow (U \in C))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.result` (`✓ std3`). ∎

*Resolves.* `Problems/bubboloni-caceres-neighbourhood-upsets` (proved) by `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bubboloni-caceres-neighbourhood-upsets","declaration_gid":"D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Daniela Bubboloni; José Cáceres (2026). *The neighbourhood convexity*. DOI: [10.48550/arXiv.2608.25912](https://doi.org/10.48550/arXiv.2608.25912). URL: <https://arxiv.org/html/2608.25912v1>.

*Commentary.*

For every finite nonempty V, every simple undirected G on V and every subset U of V, assume h(ex(K)) = K for every K in C. If x in U and B(x) contained in B(y) always imply y in U, then U belongs to C, including when U is empty. On the image L of N, polarity is an order-reversing involution with bottom S = N(V). Extreme-point generation supplies a deletable point outside each proper closed subset. Deletion induction, with covers transported by polarity, proves card(K) + card(N(K)) = card(V) + card(S) for K in L. Inclusion-exclusion then forces actual union closure in L and hence in C. Lemma 29(iii) identifies each principal upset with N(N({x})); finite unions of these principal upsets give U. The rank identity is not asserted for the extra empty set when it lies outside L.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.closedNeighbourhood`
- Truth anchor: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.common`
- Truth anchor: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.convex`
- Truth anchor: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.extremes`
- Truth anchor: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.hull`
- Truth anchor: `D5/S3/Combinatorics/Graph/BubboloniCaceresNeighbourhoodUpsets.result`
