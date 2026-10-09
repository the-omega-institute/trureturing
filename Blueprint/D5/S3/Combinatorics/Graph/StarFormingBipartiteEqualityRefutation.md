# Bipartite equality for all positive k is false

## Abstract

Bipartite equality for all positive k is false.

**Definition 1.1 (Conjecture 4.1).**

$$claim \Leftrightarrow \left(\forall n \in Nat,\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall k \in Nat,\; 1 \le k \Rightarrow \left(\operatorname{Colorable}\left(G, 2\right) \Rightarrow \operatorname{beta}\left(G, k\right) = \operatorname{SF}\left(G, k\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/StarFormingBipartiteEqualityRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rafik Sahbi, Upper k-Star-Forming Sets, k-Independence, and Upper Domination, arXiv:2610.03785v2, asserts equality for every bipartite finite graph and every positive integer k. The parameters beta and SF are the maximum k-independent cardinality and the maximum cardinality of an inclusion-minimal k-star-forming set. Graphs on Fin n represent finite simple graphs up to isomorphism.

**Theorem 1.2 (The conjectured equality is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarFormingBipartiteEqualityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sahbi-2026-star-forming-bipartite-all-k-refutation` (refuted) by `D5/S3/Combinatorics/Graph/StarFormingBipartiteEqualityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sahbi-2026-star-forming-bipartite-all-k-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/StarFormingBipartiteEqualityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Specializing the asserted equality to k equal to two gives equality for every bipartite graph at two. The ten-vertex bipartite graph has beta at most five and SF at least six, contradicting that specialization.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingBipartiteEqualityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarFormingBipartiteEqualityRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation](StarFormingDissociationRefutation.md)
