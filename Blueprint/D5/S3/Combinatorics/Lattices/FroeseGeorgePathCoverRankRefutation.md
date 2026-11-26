# A rank valley in a rooted path-cover lattice

## Abstract

A 15-element rooted poset has path-cover rank counts 15, 14, and 17 at ranks 6, 7, and 8.

**Definition 1.1 (Froese–George Question 1).**

$$\forall P \in Type,\; [\operatorname{PartialOrder}\left(P\right)] [\operatorname{OrderBot}\left(P\right)] [\operatorname{Fintype}\left(P\right)], \operatorname{LogConcave}\left(\operatorname{rankCount}\left(P\right), \operatorname{sourceHeight}\left(P\right)\right) \lor \operatorname{Unimodal}\left(\operatorname{rankCount}\left(P\right), \operatorname{sourceHeight}\left(P\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.claim` (`✓ std3`).

*Citation.* Matteus Froese and Ian George (2026). *Path Covering Spaces of Posets*. DOI: [10.48550/arXiv.2610.20890](https://doi.org/10.48550/arXiv.2610.20890). URL: <https://arxiv.org/abs/2610.20890v1>.

*Commentary.*

In Definition 2, let P be any finite partial order with a least element. At each endpoint p, partition all saturated paths from the least element to p. Include the length-zero path at the least element. Along each Hasse edge, extension must take every block at the lower endpoint into a single block at the upper endpoint. A coarser family lies below a finer family. Sum the block count minus one over all endpoints to get its rank. The height H is the same sum for the singleton partitions. Question 1 asks whether the counts r(k) of families of rank k are log-concave at every interior rank or weakly unimodal with a mode between 0 and H.

**Theorem 1.2 (Three consecutive rank counts).**

$$\operatorname{rankCount}\left(Vertex, 6\right) = 15 \land \left(\operatorname{rankCount}\left(Vertex, 7\right) = 14 \land \operatorname{rankCount}\left(Vertex, 8\right) = 17\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.witness_rank_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Matteus Froese and Ian George (2026). *Path Covering Spaces of Posets*. DOI: [10.48550/arXiv.2610.20890](https://doi.org/10.48550/arXiv.2610.20890). URL: <https://arxiv.org/abs/2610.20890v1>.

*Commentary.*

Froese and George give the product of branch downset lattices in Remark 4, using Propositions 6–7. For this witness, two incomparable vertices cover the root. Both vertices are covered by the first vertex of each of two disjoint branches. Each branch has a three-vertex stem and three leaves covering its last stem vertex. Each of the twelve branch vertices has two saturated paths from the root, distinguished by the first step. The other three vertices each have one path. Extension within a branch preserves the first step. A split successor forces its predecessor to be split, so the split vertices in each branch form a lower ideal. Conversely, each pair of lower ideals uniquely determines the compatible family, with refinement corresponding to inclusion. The rank is the combined size of the two ideals and the height is 12. Lean checks the path classification and rank-preserving equivalence for this base, then enumerates the ideal pairs to give rank counts 15, 14, and 17 at ranks 6, 7, and 8.

**Theorem 1.3 (Both shape properties fail on the same poset).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/froese-george-2026-path-cover-rank-question-1` (refuted) by `D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"froese-george-2026-path-cover-rank-question-1","declaration_gid":"D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Matteus Froese and Ian George (2026). *Path Covering Spaces of Posets*. DOI: [10.48550/arXiv.2610.20890](https://doi.org/10.48550/arXiv.2610.20890). URL: <https://arxiv.org/abs/2610.20890v1>.

*Commentary.*

The decrease from 15 to 14 requires any unimodal mode to precede rank 7. The increase from 14 to 17 requires it to follow rank 7. At rank 7, the square of 14 is 196 and the product of 15 and 17 is 255, contradicting log-concavity. This answers Question 1 for Definition 2's rooted lattice. The correspondence with count maps uses root preservation. Bare Definition 1 allows a singleton to map to the top of a two-element chain, where the path-count identity tests only the top-to-top path and the absence of a path to the bottom.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Lattices/FroeseGeorgePathCoverRankRefutation.witness_rank_counts`
