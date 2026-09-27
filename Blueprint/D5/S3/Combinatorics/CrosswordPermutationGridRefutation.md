# A Permutation Grid with 155 Rook Placements

## Abstract

The permutation 1,6,3,7,0,5,2,4 on zero-based indices gives a grid with 155 complete rook placements.

**Definition 1.1 (Decidable across relation).**

$$\forall n \in \mathrm{Nat},\; \forall W \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; \operatorname{DecidableRel}\left(\operatorname{SameAcross}\left(W\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.instDecidableRelCellSameAcross` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The finite horizontal interval condition makes the across relation decidable.

**Definition 1.2 (Decidable down relation).**

$$\forall n \in \mathrm{Nat},\; \forall W \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; \operatorname{DecidableRel}\left(\operatorname{SameDown}\left(W\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.instDecidableRelCellSameDown` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The finite vertical interval condition makes the down relation decidable.

**Definition 1.3 (Permutation grid).**

$$\forall n \in \mathrm{Nat},\; \forall w \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{permGrid}\left(w\right) = \{ c \in \operatorname{Cell}\left(n\right) | \operatorname{w}\left(c.1\right) \ne c.2\} $$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.permGrid` (`✓ std3`).

*Citation.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The black cells form the permutation matrix; every other cell is white.

**Definition 1.4 (Asserted permutation-grid counts).**

$$claim \Leftrightarrow \left(\forall r \in \mathrm{Nat},\; 0 < r \Rightarrow \left(\left(\exists n \in \mathrm{Nat},\; \exists w \in \operatorname{EquivPerm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{rookCount}\left(\operatorname{permGrid}\left(w\right)\right) = r\right) \Leftrightarrow \left(r \ne 4 \land \left(r \ne 12 \land r \bmod 4 \ne 3\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.claim` (`✓ std3`).

*Citation.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The asserted attainable positive counts exclude four, twelve, and every number congruent to three modulo four.

**Definition 1.5 (Across classes and down labels).**

$$\forall n \in \mathrm{Nat},\; \forall W \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; \operatorname{WordData}\left(n, W\right) = \{ across: \operatorname{List}\left(\operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right)\right); downId: \operatorname{Cell}\left(n\right) \to \mathrm{Nat}; downIds: \operatorname{Finset}\left(\mathrm{Nat}\right) | \left(\forall A \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; A \in across \Rightarrow A \subseteq W\right) \land \left(\left(\forall A \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; A \in across \Rightarrow \operatorname{Nonempty}\left(A\right)\right) \land \left(\left(\forall c \in \operatorname{Cell}\left(n\right),\; c \in W \Rightarrow \exists ! A \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right), A \in across \land c \in A\right) \land \left(\left(\forall c \in \operatorname{Cell}\left(n\right),\; c \in W \Rightarrow \left(\forall d \in \operatorname{Cell}\left(n\right),\; d \in W \Rightarrow \left(\operatorname{SameAcross}\left(W, c, d\right) \Leftrightarrow \left(\exists A \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; A \in across \land \left(c \in A \land d \in A\right)\right)\right)\right)\right) \land \left(\left(\forall c \in \operatorname{Cell}\left(n\right),\; c \in W \Rightarrow \left(\forall d \in \operatorname{Cell}\left(n\right),\; d \in W \Rightarrow \left(\operatorname{SameDown}\left(W, c, d\right) \Leftrightarrow \operatorname{downId}\left(c\right) = \operatorname{downId}\left(d\right)\right)\right)\right) \land \operatorname{image}\left(downId, W\right) = downIds\right)\right)\right)\right)\} $$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.WordData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

A word description consists of nonempty across classes partitioning the white cells, down labels, and their image. Common across classes and equal down labels coincide with the two word relations.

**Definition 1.6 (Perfect matching by cells).**

$$\forall n \in \mathrm{Nat},\; \forall W \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; \forall D \in \operatorname{WordData}\left(n, W\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; \operatorname{IsWordMatching}\left(D, R\right) \Leftrightarrow \left(R \subseteq W \land \left(\left(\forall A \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; A \in D.across \Rightarrow \exists ! c \in \operatorname{Cell}\left(n\right), c \in R \land c \in A\right) \land \left(\left(\forall c \in \operatorname{Cell}\left(n\right),\; c \in R \Rightarrow \left(\forall d \in \operatorname{Cell}\left(n\right),\; d \in R \Rightarrow \left(c \ne d \Rightarrow \operatorname{downId}\left(D, c\right) \ne \operatorname{downId}\left(D, d\right)\right)\right)\right) \land \operatorname{image}\left(D.downId, R\right) = D.downIds\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.IsWordMatching` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

A matching chooses exactly one cell of each across class and exactly one representative of every down label, with all chosen cells white.

**Theorem 1.7 (Placements and word matchings).**

$$\forall n \in \mathrm{Nat},\; \forall W \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; \forall D \in \operatorname{WordData}\left(n, W\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{Cell}\left(n\right)\right),\; \operatorname{IsRookPlacement}\left(W, R\right) \Leftrightarrow \operatorname{IsWordMatching}\left(D, R\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.rookPlacement_iff_wordMatching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For any exact word description, complete rook placements are precisely the perfect matchings represented by cells.

**Definition 1.8 (Recursive matching count).**

$$\forall alpha \in Type,\; \forall A \in \operatorname{Finset}\left(alpha\right),\; \forall rest \in \operatorname{List}\left(\operatorname{Finset}\left(alpha\right)\right),\; \forall id \in alpha \to \mathrm{Nat},\; \forall target \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall used \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \operatorname{matchingCount}\left([], id, target, used\right) = \operatorname{if}\left(used = target, 1, 0\right) \land \operatorname{matchingCount}\left(A :: rest, id, target, used\right) = \sum c \in A \operatorname{if}\left(\operatorname{id}\left(c\right) \in used, 0, \operatorname{matchingCount}\left(rest, id, target, \operatorname{insert}\left(\operatorname{id}\left(c\right), used\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.matchingCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Branch over the cells of the next across word, reject used down labels, and sum the counts of the remaining words. The empty list contributes one exactly when the used labels equal the target.

**Definition 1.9 (Recursive matching sets).**

$$\forall alpha \in Type,\; \forall e \in \operatorname{DecidableEq}\left(alpha\right),\; \forall A \in \operatorname{Finset}\left(alpha\right),\; \forall rest \in \operatorname{List}\left(\operatorname{Finset}\left(alpha\right)\right),\; \forall id \in alpha \to \mathrm{Nat},\; \forall target \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall used \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \operatorname{matchingSets}\left([], id, target, used\right) = \operatorname{if}\left(used = target, \left\{\left\{\right\}\right\}, \left\{\right\}\right) \land \operatorname{matchingSets}\left(A :: rest, id, target, used\right) = \operatorname{biUnion}\left(A, \lambda c: alpha. \operatorname{if}\left(\operatorname{id}\left(c\right) \in used, \left\{\right\}, \operatorname{image}\left(\operatorname{insert}\left(c\right), \operatorname{matchingSets}\left(rest, id, target, \operatorname{insert}\left(\operatorname{id}\left(c\right), used\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.matchingSets` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The same recursion forms cell sets by inserting the chosen cell into each set of the corresponding remaining branch.

**Definition 1.10 (Union of word cells).**

$$\forall alpha \in Type,\; \forall e \in \operatorname{DecidableEq}\left(alpha\right),\; \forall A \in \operatorname{Finset}\left(alpha\right),\; \forall rest \in \operatorname{List}\left(\operatorname{Finset}\left(alpha\right)\right),\; \operatorname{wordUnion}\left([]\right) = \left\{\right\} \land \operatorname{wordUnion}\left(A :: rest\right) = A \cup \operatorname{wordUnion}\left(rest\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.wordUnion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The union of an empty word list is empty; adding a first word adjoins all its cells.

**Definition 1.11 (Disjoint word classes).**

$$\forall alpha \in Type,\; \forall e \in \operatorname{DecidableEq}\left(alpha\right),\; \forall A \in \operatorname{Finset}\left(alpha\right),\; \forall rest \in \operatorname{List}\left(\operatorname{Finset}\left(alpha\right)\right),\; \left(\operatorname{DisjointWords}\left([]\right) \Leftrightarrow True\right) \land \left(\operatorname{DisjointWords}\left(A :: rest\right) \Leftrightarrow \left(\operatorname{Disjoint}\left(A, \operatorname{wordUnion}\left(rest\right)\right) \land \operatorname{DisjointWords}\left(rest\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.DisjointWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The first word is disjoint from the union of the remaining words, whose classes are recursively disjoint.

**Definition 1.12 (Partial matching conditions).**

$$\forall alpha \in Type,\; \forall e \in \operatorname{DecidableEq}\left(alpha\right),\; \forall words \in \operatorname{List}\left(\operatorname{Finset}\left(alpha\right)\right),\; \forall id \in alpha \to \mathrm{Nat},\; \forall target \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall used \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall R \in \operatorname{Finset}\left(alpha\right),\; \operatorname{SetMatchingSpec}\left(words, id, target, used, R\right) \Leftrightarrow \left(R \subseteq \operatorname{wordUnion}\left(words\right) \land \left(\left(\forall A \in \operatorname{Finset}\left(alpha\right),\; A \in words \Rightarrow \exists ! c \in alpha, c \in R \land c \in A\right) \land \left(\left(\forall c \in alpha,\; c \in R \Rightarrow \left(\forall d \in alpha,\; d \in R \Rightarrow \left(c \ne d \Rightarrow \operatorname{id}\left(c\right) \ne \operatorname{id}\left(d\right)\right)\right)\right) \land \left(\left(\forall c \in alpha,\; c \in R \Rightarrow \left(\neg \operatorname{id}\left(c\right) \in used\right)\right) \land \operatorname{image}\left(id, R\right) \cup used = target\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.SetMatchingSpec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

A partial matching stays inside the word union, meets each word once, uses distinct unused labels, and completes the target when combined with the already used labels.

**Theorem 1.13 (Removing the first chosen cell).**

$$\forall alpha \in Type,\; \forall e \in \operatorname{DecidableEq}\left(alpha\right),\; \forall A \in \operatorname{Finset}\left(alpha\right),\; \forall rest \in \operatorname{List}\left(\operatorname{Finset}\left(alpha\right)\right),\; \forall id \in alpha \to \mathrm{Nat},\; \forall target \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall used \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall R \in \operatorname{Finset}\left(alpha\right),\; \operatorname{Disjoint}\left(A, \operatorname{wordUnion}\left(rest\right)\right) \Rightarrow \left(\operatorname{SetMatchingSpec}\left(A :: rest, id, target, used, R\right) \Leftrightarrow \left(\exists c \in alpha,\; c \in A \land \left(c \in R \land \left(\left(\neg \operatorname{id}\left(c\right) \in used\right) \land \operatorname{SetMatchingSpec}\left(rest, id, target, \operatorname{insert}\left(\operatorname{id}\left(c\right), used\right), \operatorname{erase}\left(R, c\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.setMatchingSpec_cons_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

When the first word is disjoint from the remaining union, a partial matching is equivalent to choosing its cell and erasing that cell for the remaining matching.

**Theorem 1.14 (Generated cells stay in the words).**

$$\forall alpha \in Type,\; \forall e \in \operatorname{DecidableEq}\left(alpha\right),\; \forall words \in \operatorname{List}\left(\operatorname{Finset}\left(alpha\right)\right),\; \forall id \in alpha \to \mathrm{Nat},\; \forall target \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall used \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall R \in \operatorname{Finset}\left(alpha\right),\; R \in \operatorname{matchingSets}\left(words, id, target, used\right) \Rightarrow R \subseteq \operatorname{wordUnion}\left(words\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.matchingSets_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Every recursively generated cell set is a subset of the union of its word classes.

**Theorem 1.15 (Counting the generated sets).**

$$\forall alpha \in Type,\; \forall e \in \operatorname{DecidableEq}\left(alpha\right),\; \forall words \in \operatorname{List}\left(\operatorname{Finset}\left(alpha\right)\right),\; \forall id \in alpha \to \mathrm{Nat},\; \forall target \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall used \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \operatorname{DisjointWords}\left(words\right) \Rightarrow \operatorname{matchingCount}\left(words, id, target, used\right) = \operatorname{card}\left(\operatorname{matchingSets}\left(words, id, target, used\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.matchingCount_eq_card_sets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For disjoint word classes, the recursive count is the cardinality of the recursively generated cell sets.

**Theorem 1.16 (Exact partial-matching enumeration).**

$$\forall alpha \in Type,\; \forall e \in \operatorname{DecidableEq}\left(alpha\right),\; \forall words \in \operatorname{List}\left(\operatorname{Finset}\left(alpha\right)\right),\; \forall id \in alpha \to \mathrm{Nat},\; \forall target \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall used \in \operatorname{Finset}\left(\mathrm{Nat}\right),\; \forall R \in \operatorname{Finset}\left(alpha\right),\; \operatorname{DisjointWords}\left(words\right) \Rightarrow \left(R \in \operatorname{matchingSets}\left(words, id, target, used\right) \Leftrightarrow \operatorname{SetMatchingSpec}\left(words, id, target, used, R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.matchingSets_iff_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For disjoint word classes, the recursion generates exactly the cell sets satisfying the partial matching conditions.

**Definition 1.17 (Concrete permutation and inverse).**

$$\forall i \in \operatorname{Fin}\left(8\right),\; \operatorname{val}\left(\operatorname{witness}\left(i\right)\right) = \operatorname{nth}\left([1, 6, 3, 7, 0, 5, 2, 4], \operatorname{val}\left(i\right)\right) \land \operatorname{val}\left(\operatorname{invFun}\left(witness, i\right)\right) = \operatorname{nth}\left([4, 0, 6, 2, 7, 5, 1, 3], \operatorname{val}\left(i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.witness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The permutation has values 1,6,3,7,0,5,2,4 and inverse values 4,0,6,2,7,5,1,3 on zero-based indices.

**Definition 1.18 (Concrete row interval).**

$$\forall i \in \mathrm{Nat},\; \forall lo \in \mathrm{Nat},\; \forall hi \in \mathrm{Nat},\; \operatorname{rowRun}\left(i, lo, hi\right) = \{ c \in \operatorname{Cell}\left(8\right) | \operatorname{val}\left(c.1\right) = i \land \left(lo \le \operatorname{val}\left(c.2\right) \land \operatorname{val}\left(c.2\right) \le hi\right)\} $$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.rowRun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

A row interval contains exactly the cells with the specified row and columns between the inclusive endpoints.

**Definition 1.19 (Fourteen across words).**

$$witnessAcross = [\operatorname{rowRun}\left(0, 0, 0\right), \operatorname{rowRun}\left(0, 2, 7\right), \operatorname{rowRun}\left(1, 0, 5\right), \operatorname{rowRun}\left(1, 7, 7\right), \operatorname{rowRun}\left(2, 0, 2\right), \operatorname{rowRun}\left(2, 4, 7\right), \operatorname{rowRun}\left(3, 0, 6\right), \operatorname{rowRun}\left(4, 1, 7\right), \operatorname{rowRun}\left(5, 0, 4\right), \operatorname{rowRun}\left(5, 6, 7\right), \operatorname{rowRun}\left(6, 0, 1\right), \operatorname{rowRun}\left(6, 3, 7\right), \operatorname{rowRun}\left(7, 0, 3\right), \operatorname{rowRun}\left(7, 5, 7\right)]$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.witnessAcross` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The listed row intervals are the fourteen maximal across words of the concrete permutation grid.

**Definition 1.20 (Fourteen down-word labels).**

$$\forall c \in \operatorname{Cell}\left(8\right),\; \operatorname{witnessDownId}\left(c\right) = \operatorname{if}\left(\operatorname{val}\left(c.2\right) = 0, \operatorname{if}\left(\operatorname{val}\left(c.1\right) \le 3, 0, 1\right), \operatorname{if}\left(\operatorname{val}\left(c.2\right) = 1, 2, \operatorname{if}\left(\operatorname{val}\left(c.2\right) = 2, \operatorname{if}\left(\operatorname{val}\left(c.1\right) \le 5, 3, 4\right), \operatorname{if}\left(\operatorname{val}\left(c.2\right) = 3, \operatorname{if}\left(\operatorname{val}\left(c.1\right) \le 1, 5, 6\right), \operatorname{if}\left(\operatorname{val}\left(c.2\right) = 4, 7, \operatorname{if}\left(\operatorname{val}\left(c.2\right) = 5, \operatorname{if}\left(\operatorname{val}\left(c.1\right) \le 4, 8, 9\right), \operatorname{if}\left(\operatorname{val}\left(c.2\right) = 6, \operatorname{if}\left(\operatorname{val}\left(c.1\right) = 0, 10, 11\right), \operatorname{if}\left(\operatorname{val}\left(c.1\right) \le 2, 12, 13\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.witnessDownId` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Each column is labelled on the white runs above and below its black cell; the two boundary black cells leave just one white run in their columns.

**Theorem 1.21 (The matching count is 155).**

$$\operatorname{matchingCount}\left(witnessAcross, witnessDownId, \operatorname{range}\left(14\right), \left\{\right\}\right) = 155$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.witness_matchingCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Starting with no used labels and target labels zero through thirteen, the concrete word recursion counts 155 matchings.

**Definition 1.22 (Exact words of the concrete grid).**

$$witnessData: \operatorname{WordData}\left(8, \operatorname{permGrid}\left(witness\right)\right) \land \left(witnessData.across = witnessAcross \land \left(witnessData.downId = witnessDownId \land witnessData.downIds = \operatorname{range}\left(14\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.witnessData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The concrete across intervals and down labels satisfy all word-description conditions for the white cells of the permutation grid.

**Theorem 1.23 (The asserted count criterion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lewis-won-permutation-grid-counts-refutation` (refuted) by `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lewis-won-permutation-grid-counts-refutation","declaration_gid":"D5/S3/Combinatorics/CrosswordPermutationGridRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The concrete grid has 155 complete rook placements, and 155 is congruent to three modulo four, contradicting the asserted criterion.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.DisjointWords`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.IsWordMatching`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.SetMatchingSpec`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.WordData`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.instDecidableRelCellSameAcross`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.instDecidableRelCellSameDown`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.matchingCount`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.matchingCount_eq_card_sets`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.matchingSets`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.matchingSets_iff_spec`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.matchingSets_subset`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.permGrid`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.rookPlacement_iff_wordMatching`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.rowRun`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.setMatchingSpec_cons_iff`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.witness`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.witnessAcross`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.witnessData`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.witnessDownId`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.witness_matchingCount`
- Truth anchor: `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.wordUnion`
- Dependency: [D5/S3/Combinatorics/CrosswordRookCountsDefs](CrosswordRookCountsDefs.md)
