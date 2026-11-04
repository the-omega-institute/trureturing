# Coarse three-block partition refinements, triangular inversion, and bipartite masked ranks

## Abstract

Refinement counts between two- and three-block finite set partitions invert the upper-sum operator on coarse partitions and double the off-diagonal rank of symmetric binary matrices across bipartitions.

On the poset of set partitions of Fin q ordered by refinement (rho <= sigma when every block of rho lies in a block of sigma), the two-block and three-block strata form a two-step upper interval beneath the trivial one-block partition. Counting three-block refinements of each two-block partition expresses the unweighted sum over two- and three-block partitions as a linear combination of upper sums, proves triangular surjectivity of the refinement-transpose weight map, shows that upper sums on two- and three-block partitions determine all upper sums, and identifies the F2-rank of a bipartition-masked symmetric matrix as twice the rank of its off-diagonal rectangular block.

**Definition 1.1 (Finite party partitions).**

$$\forall (q : \mathbb{N}), \mathrm{PartyPartition}\left(q\right) = \mathrm{Finpartition}\left((\mathrm{univ} : \mathrm{Finset}\left(\mathrm{Fin}\left(q\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.PartyPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A party partition of Fin q is a finite partition of Finset.univ into pairwise disjoint nonempty blocks whose union is all of Fin q, ordered by block refinement.

**Definition 1.2 (Stratum of k-block partitions).**

$$\forall (q : \mathbb{N}), \forall (k : \mathbb{N}), \mathrm{partitionsOfCard}\left(q, k\right) = \mathrm{filter}\left((\mathrm{univ} : \mathrm{Finset}\left(\mathrm{PartyPartition}\left(q\right)\right)), (\pi : \mathrm{PartyPartition}\left(q\right)) \mapsto \mathrm{card}\left(\mathrm{parts}\left(\pi\right)\right) = k\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.partitionsOfCard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filters the finite set of all partitions of Fin q to those with exactly k nonempty blocks.

**Definition 1.3 (Coarse two- and three-block partitions).**

$$\forall (q : \mathbb{N}), \mathrm{twoOrThreePartitions}\left(q\right) = \mathrm{partitionsOfCard}\left(q, 2\right) \cup \mathrm{partitionsOfCard}\left(q, 3\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.twoOrThreePartitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The union of the two-block and three-block partition strata of Fin q.

**Definition 1.4 (Partitions with at least two blocks).**

$$\forall (q : \mathbb{N}), \mathrm{nontrivialPartitions}\left(q\right) = \mathrm{filter}\left((\mathrm{univ} : \mathrm{Finset}\left(\mathrm{PartyPartition}\left(q\right)\right)), (\pi : \mathrm{PartyPartition}\left(q\right)) \mapsto 2 \leq \mathrm{card}\left(\mathrm{parts}\left(\pi\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.nontrivialPartitions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Collects all partitions of Fin q having two or more blocks, excluding only the indiscrete one-block partition when q >= 1.

**Definition 1.5 (Bundled block of an element).**

$$\forall (q : \mathbb{N}), \forall (\pi : \mathrm{PartyPartition}\left(q\right)), \forall (c : \mathrm{Fin}\left(q\right)), \mathrm{val}\left((\mathrm{partOf}\left(\pi, c\right) : \mathrm{parts}\left(\pi\right))\right) = \mathrm{part}\left(\pi, c\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.partOf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Maps each element c in Fin q to the unique block of pi containing c, typed as a member of pi.parts.

**Definition 1.6 (Coarse-grained colouring along a block listing).**

$$\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (k : \mathbb{N}), \forall (\pi : \mathrm{PartyPartition}\left(q\right)), \forall (B : \mathrm{Equiv}\left(\mathrm{Fin}\left(k\right), \mathrm{parts}\left(\pi\right)\right)), \forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (u : \mathrm{Fin}\left(N\right)), \mathrm{coarseCol}\left(\pi, B, col, u\right) = \mathrm{symm}\left(B, \mathrm{partOf}\left(\pi, col(u)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.coarseCol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Composes a colouring col : Fin N to Fin q with the block map of pi and the inverse of an equivalence B : Fin k to pi.parts.

**Definition 1.7 (Partition-masked binary matrix).**

$$\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (\pi : \mathrm{PartyPartition}\left(q\right)), \forall (u : \mathrm{Fin}\left(N\right)), \forall (v : \mathrm{Fin}\left(N\right)), \mathrm{maskedAdj}\left(\Gamma, col, \pi, u, v\right) = \mathrm{ite}\left(\mathrm{part}\left(\pi, col(u)\right) = \mathrm{part}\left(\pi, col(v)\right), 0, \Gamma(u, v)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.maskedAdj` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Zeroes entries of Gamma whose row and column indices are assigned by col to the same block of pi, retaining entries across distinct blocks.

**Definition 1.8 (Rank of the partition-masked matrix).**

$$\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (\pi : \mathrm{PartyPartition}\left(q\right)), \mathrm{partitionRank}\left(\Gamma, col, \pi\right) = \mathrm{rank}\left(\mathrm{maskedAdj}\left(\Gamma, col, \pi\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.partitionRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix rank over ZMod 2 of maskedAdj(Gamma, col, pi).

**Definition 1.9 (Off-diagonal rectangular submatrix across two party subsets).**

$$\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (X : \mathrm{Finset}\left(\mathrm{Fin}\left(q\right)\right)), \forall (Y : \mathrm{Finset}\left(\mathrm{Fin}\left(q\right)\right)), \forall (u : \{x : \mathrm{Fin}\left(N\right) \mid col(x) \in X\}), \forall (v : \{y : \mathrm{Fin}\left(N\right) \mid col(y) \in Y\}), \mathrm{offDiagBlock}\left(\Gamma, col, X, Y, u, v\right) = \Gamma(\mathrm{val}\left(u\right), \mathrm{val}\left(v\right))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.offDiagBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restricts Gamma to rows whose colour lies in X and columns whose colour lies in Y.

**Definition 1.10 (Upper sum over two- and three-block coarsenings).**

$$\forall (q : \mathbb{N}), \forall (r : (\mathrm{PartyPartition}\left(q\right) \to \mathbb{R})), \forall (\rho : \mathrm{PartyPartition}\left(q\right)), \mathrm{upperRankSum}\left(r, \rho\right) = \sum_{\sigma \in \mathrm{twoOrThreePartitions}\left(q\right) \land (\rho \leq \sigma)} r(\sigma)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.upperRankSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sums a real-valued function r over all two- and three-block partitions sigma of Fin q refined by rho.

**Definition 1.11 (Weighted refinement sum on a coarse partition).**

$$\forall (q : \mathbb{N}), \forall (c : (\mathrm{PartyPartition}\left(q\right) \to \mathbb{R})), \forall (\sigma : \mathrm{PartyPartition}\left(q\right)), \mathrm{coarseWeight}\left(c, \sigma\right) = \sum_{\rho \in \mathrm{nontrivialPartitions}\left(q\right) \land (\rho \leq \sigma)} 3^{(2 - (\mathrm{card}\left(\mathrm{parts}\left(\rho\right)\right) : \mathbb{Z}))} \cdot c(\rho)$$

*Formalization.* `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.coarseWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Aggregates c(rho) weighted by the integer power 3^{2 - |rho|} over all partitions rho <= sigma with at least two blocks.

**Theorem 1.12 (Stirling identities, k-block partition cardinality, and three-block refinements of a bipartition).**

$$(\forall (m : \mathbb{N}), 1 \leq m \Rightarrow (\mathrm{stirlingSecond}\left(m, 2\right) = (2^{(m - 1)} - 1))) \land (\forall (q : \mathbb{N}), 1 \leq q \Rightarrow ((2 \cdot (\mathrm{stirlingSecond}\left(q, 2\right) + \mathrm{stirlingSecond}\left(q, 3\right)) = (3^{(q - 1)} - 1)) \land (\frac{((3 : \mathbb{R})^{(q - 1)} - 1)}{2} = (\mathrm{stirlingSecond}\left(q, 2\right) : \mathbb{R}) + (\mathrm{stirlingSecond}\left(q, 3\right) : \mathbb{R})))) \land (\forall (q : \mathbb{N}), \forall (k : \mathbb{N}), \mathrm{card}\left(\mathrm{partitionsOfCard}\left(q, k\right)\right) = \mathrm{stirlingSecond}\left(q, k\right)) \land (\forall (q : \mathbb{N}), \forall (\sigma : \mathrm{PartyPartition}\left(q\right)), \sigma \in \mathrm{partitionsOfCard}\left(q, 2\right) \Rightarrow (\mathrm{card}\left(\mathrm{filter}\left(\mathrm{partitionsOfCard}\left(q, 3\right), (\pi : \mathrm{PartyPartition}\left(q\right)) \mapsto \pi \leq \sigma\right)\right) + 2 = \sum_{B \in \mathrm{parts}\left(\sigma\right)} 2^{(\mathrm{card}\left(B\right) - 1)}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.stirling_and_three_block_refinement_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Establishes S(m, 2) = 2^{m-1} - 1 for m >= 1 and 2(S(q, 2) + S(q, 3)) = 3^{q-1} - 1 for q >= 1 by induction on the Stirling recurrence, proves |partitionsOfCard(q, k)| = S(q, k) by counting functions Fin q to Fin k fibrewise by kernel partition and injective block colouring against the falling-factorial power expansion, and proves that every two-block partition sigma = {X, Y} has S(|X|, 2) + S(|Y|, 2) = 2^{|X|-1} + 2^{|Y|-1} - 2 three-block refinements obtained by keeping one block intact and splitting the other into two nonempty parts.

**Theorem 1.13 (Upper-sum reduction, poset Fubini identity, triangular surjectivity, and coarse determination).**

$$(\forall (q : \mathbb{N}), 3 \leq q \Rightarrow (\forall (r : (\mathrm{PartyPartition}\left(q\right) \to \mathbb{R})), \sum_{\sigma \in \mathrm{twoOrThreePartitions}\left(q\right)} r(\sigma) = \sum_{\pi \in \mathrm{partitionsOfCard}\left(q, 3\right)} \mathrm{upperRankSum}\left(r, \pi\right) + \sum_{\sigma \in \mathrm{partitionsOfCard}\left(q, 2\right)} (3 - \sum_{B \in \mathrm{parts}\left(\sigma\right)} 2^{(\mathrm{card}\left(B\right) - 1)}) \cdot \mathrm{upperRankSum}\left(r, \sigma\right))) \land (\forall (q : \mathbb{N}), \forall (c : (\mathrm{PartyPartition}\left(q\right) \to \mathbb{R})), \forall (r : (\mathrm{PartyPartition}\left(q\right) \to \mathbb{R})), \sum_{\rho \in \mathrm{nontrivialPartitions}\left(q\right)} c(\rho) \cdot (3^{(2 - (\mathrm{card}\left(\mathrm{parts}\left(\rho\right)\right) : \mathbb{Z}))} \cdot \mathrm{upperRankSum}\left(r, \rho\right)) = \sum_{\sigma \in \mathrm{twoOrThreePartitions}\left(q\right)} \mathrm{coarseWeight}\left(c, \sigma\right) \cdot r(\sigma)) \land (\forall (q : \mathbb{N}), \forall (w : (\mathrm{PartyPartition}\left(q\right) \to \mathbb{R})), \exists (c : (\mathrm{PartyPartition}\left(q\right) \to \mathbb{R})), (\forall (\rho : \mathrm{PartyPartition}\left(q\right)), \neg(\rho \in \mathrm{twoOrThreePartitions}\left(q\right)) \Rightarrow (c(\rho) = 0)) \land (\forall (\sigma : \mathrm{PartyPartition}\left(q\right)), \sigma \in \mathrm{twoOrThreePartitions}\left(q\right) \Rightarrow (\mathrm{coarseWeight}\left(c, \sigma\right) = w(\sigma)))) \land (\forall (q : \mathbb{N}), \forall (rA : (\mathrm{PartyPartition}\left(q\right) \to \mathbb{R})), \forall (rB : (\mathrm{PartyPartition}\left(q\right) \to \mathbb{R})), ((\forall (\sigma : \mathrm{PartyPartition}\left(q\right)), \sigma \in \mathrm{partitionsOfCard}\left(q, 2\right) \Rightarrow (\mathrm{upperRankSum}\left(rA, \sigma\right) = \mathrm{upperRankSum}\left(rB, \sigma\right))) \land (\forall (\pi : \mathrm{PartyPartition}\left(q\right)), \pi \in \mathrm{partitionsOfCard}\left(q, 3\right) \Rightarrow (\mathrm{upperRankSum}\left(rA, \pi\right) = \mathrm{upperRankSum}\left(rB, \pi\right)))) \Rightarrow ((\forall (\sigma : \mathrm{PartyPartition}\left(q\right)), \sigma \in \mathrm{twoOrThreePartitions}\left(q\right) \Rightarrow (rA(\sigma) = rB(\sigma))) \land (\forall (\rho : \mathrm{PartyPartition}\left(q\right)), \mathrm{upperRankSum}\left(rA, \rho\right) = \mathrm{upperRankSum}\left(rB, \rho\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.coarse_upper_sum_reduction_and_triangular_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For q >= 3, every three-block partition pi has upperRankSum(r, pi) = r(pi) + sum_{sigma in Pi_2(q), pi <= sigma} r(sigma) while every two-block partition sigma has upperRankSum(r, sigma) = r(sigma); exchanging the order of summation counts each two-block sigma once per three-block refinement, giving coefficient 1 - (2^{|X|-1} + 2^{|Y|-1} - 2) = 3 - 2^{|X|-1} - 2^{|Y|-1}. Exchanging summation over rho <= sigma yields the transpose identity pairing upperRankSum against coarseWeight. Because coarseWeight is triangular with nonzero diagonal entries 1 on Pi_2(q) and 1/3 on Pi_3(q), explicit back-substitution produces a preimage c supported on twoOrThreePartitions(q) for any target weight w, while matching upper sums on Pi_2(q) and Pi_3(q) uniquely determine r on twoOrThreePartitions(q) and hence upperRankSum(r, rho) for every partition rho.

**Theorem 1.14 (Rank doubling for symmetric matrices masked by a two-block partition).**

$$\forall (N : \mathbb{N}), \forall (q : \mathbb{N}), \forall (\Gamma : \mathrm{Matrix}\left(\mathrm{Fin}\left(N\right), \mathrm{Fin}\left(N\right), \mathrm{ZMod}\left(2\right)\right)), \mathrm{IsSymm}\left(\Gamma\right) \Rightarrow (\forall (col : (\mathrm{Fin}\left(N\right) \to \mathrm{Fin}\left(q\right))), \forall (\sigma : \mathrm{PartyPartition}\left(q\right)), \sigma \in \mathrm{partitionsOfCard}\left(q, 2\right) \Rightarrow (\forall (X : \mathrm{Finset}\left(\mathrm{Fin}\left(q\right)\right)), \forall (Y : \mathrm{Finset}\left(\mathrm{Fin}\left(q\right)\right)), ((\mathrm{parts}\left(\sigma\right) = \mathrm{pair}\left(X, Y\right)) \land (X \neq Y)) \Rightarrow (\mathrm{partitionRank}\left(\Gamma, col, \sigma\right) = 2 \cdot \mathrm{rank}\left(\mathrm{offDiagBlock}\left(\Gamma, col, X, Y\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.bipartite_masked_antidiagonal_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a symmetric matrix Gamma over ZMod 2 and a two-block partition sigma with distinct blocks X and Y, reindexing Fin N by the disjoint union of the X-coloured and Y-coloured coordinates conjugates maskedAdj(Gamma, col, sigma) to the block anti-diagonal matrix [[0, B], [B^T, 0]] where B = offDiagBlock(Gamma, col, X, Y). Its column space splits as the direct sum of range(B) and range(B^T), so rank(maskedAdj) = rank(B) + rank(B^T) = 2 rank(B).

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.PartyPartition`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.bipartite_masked_antidiagonal_rank`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.coarseCol`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.coarseWeight`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.coarse_upper_sum_reduction_and_triangular_inversion`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.maskedAdj`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.nontrivialPartitions`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.offDiagBlock`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.partOf`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.partitionRank`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.partitionsOfCard`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.stirling_and_three_block_refinement_count`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.twoOrThreePartitions`
- Truth anchor: `D5/S3/Combinatorics/Partitions/CoarseThreeBlockRefinement.upperRankSum`
