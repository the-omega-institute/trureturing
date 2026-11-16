# Two-independence and upper two-star formation differ

## Abstract

A bipartite graph on ten vertices has a minimal two-star-forming set of size six, but every two-independent set has size at most five.

Let G be a finite simple graph on V, with decidable adjacency. Write d(G,S,v) for the number of neighbours of v in S. All sets below are finite vertex sets. The definitions are those of Rafik Sahbi, Upper k-Star-Forming Sets, k-Independence, and Upper Domination, arXiv:2610.03785v2, Definition 2.1 and Conjecture 4.2.

**Theorem 1.1 (The original H0 certificate).**

Lean statement: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.h0_properties`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.h0_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original ten-vertex graph is two-colorable, its selected six-set is inclusion-minimal two-star-forming, and beta two is at most five. These are the same proof bodies consumed by result, exposed for arbitrary port compositions. The public edges, counterGraph and selected definitions retain the original vertex labels, neighborhoods and selected set.

**Definition 1.2 (Equality on all bipartite finite graphs).**

$$claim \Leftrightarrow \left(\forall n \in Nat,\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{Colorable}\left(G, 2\right) \Rightarrow \operatorname{beta}\left(G, 2\right) = \operatorname{SF}\left(G, 2\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjecture 4.2 asserts equality for every bipartite finite graph. Graphs on Fin n cover every finite simple graph up to isomorphism. Bipartiteness is expressed by a proper colouring with two colours.

**Theorem 1.3 (The equality is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sahbi-2026-star-forming-bipartite-refutation` (refuted) by `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sahbi-2026-star-forming-bipartite-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Use vertices 0 through 9, with sides 0 through 4 and 5 through 9. The neighbourhoods on the first side are {5,6,9}, {5,6,8}, {8,9}, {6,7,8,9}, and {5,7,8,9}, respectively. Colour by side. The set {0,1,2,5,6,7} satisfies the local criterion, while each of its 63 proper subsets fails it. It is therefore minimal two-star-forming, so SF is at least six. Each of the 210 six-element vertex sets contains a vertex with at least two selected neighbours. Any larger two-independent set would contain a two-independent six-element subset, since deletion cannot increase selected degrees. Thus beta is at most five and the asserted equality fails.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.h0_properties`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Foundations/Invariants](StarForming/Foundations/Invariants.md)
