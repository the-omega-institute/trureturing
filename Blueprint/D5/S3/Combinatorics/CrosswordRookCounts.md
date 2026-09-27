# Every Natural Rook-Placement Count Occurs

## Abstract

An alternating five-column family realizes every positive count, and a three-by-three grid realizes zero.

**Theorem 1.1 (Horizontal row intervals).**

$$\forall r \in \mathrm{Nat},\; \forall c \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \forall d \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \left(c \in \operatorname{white}\left(r\right) \land \left(d \in \operatorname{white}\left(r\right) \land c.1 = d.1\right)\right) \Rightarrow \operatorname{SameAcross}\left(\operatorname{white}\left(r\right), c, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.white_same_across` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Two white cells in the same row of the family lie in the same across word.

**Theorem 1.2 (Side-word confinement).**

$$\forall r \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \forall c \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \forall d \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \left(\left(2 \cdot i \le \operatorname{val}\left(c.1\right) \land \operatorname{val}\left(c.1\right) \le 2 \cdot i + 2\right) \land \left(\operatorname{val}\left(c.2\right) = \operatorname{side}\left(i\right) \land \operatorname{SameDown}\left(\operatorname{white}\left(r\right), c, d\right)\right)\right) \Rightarrow \left(2 \cdot i \le \operatorname{val}\left(d.1\right) \land \operatorname{val}\left(d.1\right) \le 2 \cdot i + 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.side_word_stays_in_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

A down word meeting the side column within a block remains between that block's first and last rows.

**Theorem 1.3 (Singleton outer words).**

$$\forall r \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \forall c \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \forall d \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \left(\operatorname{val}\left(c.1\right) = 2 \cdot i + 1 \land \left(\operatorname{val}\left(c.2\right) = \operatorname{tip}\left(i\right) \land \operatorname{SameDown}\left(\operatorname{white}\left(r\right), c, d\right)\right)\right) \Rightarrow c = d$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.tip_word_is_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

A down word through an outer tip contains only that tip.

**Theorem 1.4 (Odd-row white columns).**

$$\forall r \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; i + 1 < r \Rightarrow \left(\left(2 \cdot i + 1 < 2 \cdot r - 1 \land \left(\operatorname{rowLeft}\left(r, 2 \cdot i + 1\right) \le b \land b \le \operatorname{rowRight}\left(r, 2 \cdot i + 1\right)\right)\right) \Leftrightarrow \left(b = 2 \lor \left(b = \operatorname{side}\left(i\right) \lor b = \operatorname{tip}\left(i\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.odd_row_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Each occupied odd row consists of the central, side, and outer columns of its block.

**Theorem 1.5 (Even-row white columns).**

$$\forall r \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \forall b \in \mathrm{Nat},\; i < r \Rightarrow \left(\left(2 \cdot i < 2 \cdot r - 1 \land \left(\operatorname{rowLeft}\left(r, 2 \cdot i\right) \le b \land b \le \operatorname{rowRight}\left(r, 2 \cdot i\right)\right)\right) \Leftrightarrow \left(b = 2 \lor \left(\left(0 < i \land b = \operatorname{side}\left(i - 1\right)\right) \lor \left(i + 1 < r \land b = \operatorname{side}\left(i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.even_row_columns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Each occupied even row meets the central column and the side columns of the blocks incident to it.

**Theorem 1.6 (Spine, side runs, and tips).**

$$\forall r \in \mathrm{Nat},\; \forall c \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; c \in \operatorname{white}\left(r\right) \Leftrightarrow \left(\left(\operatorname{val}\left(c.1\right) < 2 \cdot r - 1 \land \operatorname{val}\left(c.2\right) = 2\right) \lor \left(\left(\exists i \in \mathrm{Nat},\; i + 1 < r \land \left(\operatorname{val}\left(c.2\right) = \operatorname{side}\left(i\right) \land \left(2 \cdot i \le \operatorname{val}\left(c.1\right) \land \operatorname{val}\left(c.1\right) \le 2 \cdot i + 2\right)\right)\right) \lor \left(\exists i \in \mathrm{Nat},\; i + 1 < r \land \left(\operatorname{val}\left(c.1\right) = 2 \cdot i + 1 \land \operatorname{val}\left(c.2\right) = \operatorname{tip}\left(i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.white_iff_pattern` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The white cells are precisely the central spine, the three-cell side runs, and the outer tips.

**Theorem 1.7 (Classification of down words).**

$$\forall r \in \mathrm{Nat},\; \forall c \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \forall d \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \left(c \in \operatorname{white}\left(r\right) \land d \in \operatorname{white}\left(r\right)\right) \Rightarrow \left(\operatorname{SameDown}\left(\operatorname{white}\left(r\right), c, d\right) \Leftrightarrow \left(\left(\operatorname{val}\left(c.2\right) = 2 \land \operatorname{val}\left(d.2\right) = 2\right) \lor \left(\left(\exists i \in \mathrm{Nat},\; i + 1 < r \land \left(\operatorname{val}\left(c.2\right) = \operatorname{side}\left(i\right) \land \left(\operatorname{val}\left(d.2\right) = \operatorname{side}\left(i\right) \land \left(\left(2 \cdot i \le \operatorname{val}\left(c.1\right) \land \operatorname{val}\left(c.1\right) \le 2 \cdot i + 2\right) \land \left(2 \cdot i \le \operatorname{val}\left(d.1\right) \land \operatorname{val}\left(d.1\right) \le 2 \cdot i + 2\right)\right)\right)\right)\right) \lor c = d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.same_down_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Two white cells share a down word exactly when both are central, both lie in one side block, or they coincide.

**Theorem 1.8 (At most one candidate rook per row).**

$$\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall c \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \forall d \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \left(c \in \operatorname{candidate}\left(r, k\right) \land \left(d \in \operatorname{candidate}\left(r, k\right) \land c.1 = d.1\right)\right) \Rightarrow c = d$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.candidate_row_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Candidate cells with the same row index are equal.

**Theorem 1.9 (Selected side endpoint).**

$$\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall i \in \mathrm{Nat},\; \forall c \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \left(c \in \operatorname{candidate}\left(r, k\right) \land \left(\operatorname{val}\left(c.2\right) = \operatorname{side}\left(i\right) \land \left(2 \cdot i \le \operatorname{val}\left(c.1\right) \land \operatorname{val}\left(c.1\right) \le 2 \cdot i + 2\right)\right)\right) \Rightarrow \left(\left(i < k \land \operatorname{val}\left(c.1\right) = 2 \cdot i\right) \lor \left(k \le i \land \operatorname{val}\left(c.1\right) = 2 \cdot i + 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.candidate_side_choice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

A candidate cell in a side block is its top endpoint before the central index and its bottom endpoint afterward.

**Theorem 1.10 (Candidate across-word coverage).**

$$\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall a \in \operatorname{Fin}\left(\operatorname{gridSize}\left(r\right)\right),\; \left(k < r \land \operatorname{val}\left(a\right) < 2 \cdot r - 1\right) \Rightarrow \left(\exists d \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; d \in \operatorname{candidate}\left(r, k\right) \land d.1 = a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.candidate_row_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For k less than r, every occupied row contains a candidate rook.

**Theorem 1.11 (Candidate down-word coverage).**

$$\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall c \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \left(k < r \land c \in \operatorname{white}\left(r\right)\right) \Rightarrow \left(\exists d \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; d \in \operatorname{candidate}\left(r, k\right) \land \operatorname{SameDown}\left(\operatorname{white}\left(r\right), c, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.candidate_down_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For k less than r, every white cell shares its down word with a candidate rook.

**Theorem 1.12 (Candidate completeness).**

$$\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; k < r \Rightarrow \operatorname{IsRookPlacement}\left(\operatorname{white}\left(r\right), \operatorname{candidate}\left(r, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.candidate_is_placement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Every central index less than r gives a complete non-attacking rook placement.

**Theorem 1.13 (Forced upper endpoints).**

$$\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall R \in \operatorname{Finset}\left(\operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right)\right),\; \forall u \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \left(\operatorname{IsRookPlacement}\left(\operatorname{white}\left(r\right), R\right) \land \left(u \in R \land \left(\operatorname{val}\left(u.1\right) = 2 \cdot k \land \operatorname{val}\left(u.2\right) = 2\right)\right)\right) \Rightarrow \left(\forall i \in \mathrm{Nat},\; i + 1 < r \Rightarrow \left(i < k \Rightarrow \left(\exists d \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; d \in R \land \left(\operatorname{val}\left(d.1\right) = 2 \cdot i \land \operatorname{val}\left(d.2\right) = \operatorname{side}\left(i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.placement_top_before_central` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

In any complete placement with a central rook in row two k, every earlier side block uses its upper endpoint.

**Theorem 1.14 (Forced lower endpoints).**

$$\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall R \in \operatorname{Finset}\left(\operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right)\right),\; \forall u \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; \left(\operatorname{IsRookPlacement}\left(\operatorname{white}\left(r\right), R\right) \land \left(u \in R \land \left(\operatorname{val}\left(u.1\right) = 2 \cdot k \land \operatorname{val}\left(u.2\right) = 2\right)\right)\right) \Rightarrow \left(\forall i \in \mathrm{Nat},\; i + 1 < r \Rightarrow \left(k \le i \Rightarrow \left(\exists d \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right),\; d \in R \land \left(\operatorname{val}\left(d.1\right) = 2 \cdot i + 2 \land \operatorname{val}\left(d.2\right) = \operatorname{side}\left(i\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.placement_bottom_after_central` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

In any complete placement with a central rook in row two k, every side block from k onward uses its lower endpoint.

**Theorem 1.15 (Exhaustion by central indices).**

$$\forall r \in \mathrm{Nat},\; \forall R \in \operatorname{Finset}\left(\operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right)\right),\; \left(0 < r \land \operatorname{IsRookPlacement}\left(\operatorname{white}\left(r\right), R\right)\right) \Rightarrow \left(\exists k \in \mathrm{Nat},\; k < r \land R = \operatorname{candidate}\left(r, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.placement_eq_candidate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

For positive r, every complete placement equals the candidate for some k less than r.

**Theorem 1.16 (Distinct central choices).**

$$\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall l \in \mathrm{Nat},\; \left(k < r \land \left(l < r \land \operatorname{candidate}\left(r, k\right) = \operatorname{candidate}\left(r, l\right)\right)\right) \Rightarrow k = l$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.candidate_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Equal candidates with indices less than r have equal indices.

**Definition 1.17 (The zero-count grid).**

$$zeroWhite = \left\{(0, 1), (0, 2), (1, 0), (2, 0)\right\}$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCounts.zeroWhite` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The white cells are two adjacent cells in the first row and two vertically adjacent cells in the first column.

**Theorem 1.18 (No placement on the zero grid).**

$$\operatorname{rookCount}\left(zeroWhite\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.zero_rook_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The two singleton down words in the first row would force two rooks in one across word, so the count is zero.

**Theorem 1.19 (Every natural number occurs).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CrosswordRookCounts.result` (`✓ std3`). ∎

*Resolves.* `Problems/lewis-won-crossword-rook-counts` (proved) by `D5/S3/Combinatorics/CrosswordRookCounts.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lewis-won-crossword-rook-counts","declaration_gid":"D5/S3/Combinatorics/CrosswordRookCounts.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The zero grid and the positive family together realize every natural rook-placement count on square grids.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.candidate_down_exists`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.candidate_injective`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.candidate_is_placement`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.candidate_row_exists`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.candidate_row_unique`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.candidate_side_choice`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.even_row_columns`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.odd_row_columns`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.placement_bottom_after_central`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.placement_eq_candidate`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.placement_top_before_central`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.result`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.same_down_iff`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.side_word_stays_in_block`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.tip_word_is_singleton`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.white_iff_pattern`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.white_same_across`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.zeroWhite`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCounts.zero_rook_count`
- Dependency: [D5/S3/Combinatorics/CrosswordRookCountsDefs](CrosswordRookCountsDefs.md)
