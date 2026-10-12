# Triangle-free equality at two is false

## Abstract

Triangle-free equality at two is false.

**Definition 1.1 (Conjecture 7.2).**

$$claim \Leftrightarrow \left(\forall n \in Nat,\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{CliqueFree}\left(G, 3\right) \Rightarrow \operatorname{beta}\left(G, 2\right) = \operatorname{SF}\left(G, 2\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rafik Sahbi, Upper k-Star-Forming Sets, k-Independence, and Upper Domination, arXiv:2610.03785v2, asserts equality at two for every triangle-free finite graph. The parameters beta and SF are the maximum k-independent cardinality and the maximum cardinality of an inclusion-minimal k-star-forming set. Graphs on Fin n represent finite simple graphs up to isomorphism.

**Theorem 1.2 (The conjectured equality is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sahbi-2026-star-forming-triangle-free-refutation` (refuted) by `D5/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sahbi-2026-star-forming-triangle-free-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

A proper colouring with two colours excludes a clique on three vertices. Thus equality for every triangle-free graph would imply equality for every bipartite graph at k equal to two. The ten-vertex bipartite graph has beta at most five and SF at least six, contradicting that equality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation](StarFormingDissociationRefutation.md)
