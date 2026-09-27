# Crossword Grids and Rook Placements

## Abstract

Complete rook placements meet every maximal horizontal and vertical white run exactly once.

**Definition 1.1 (Square-grid cell).**

$$\forall N \in \mathrm{Nat},\; \operatorname{Cell}\left(N\right) = \operatorname{Fin}\left(N\right) \times \operatorname{Fin}\left(N\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.Cell` (`✓ std3`).

*Citation.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

A cell is a pair of finite row and column indices.

**Definition 1.2 (Common across word).**

$$\forall N \in \mathrm{Nat},\; \forall W \in \operatorname{Finset}\left(\operatorname{Cell}\left(N\right)\right),\; \forall c \in \operatorname{Cell}\left(N\right),\; \forall d \in \operatorname{Cell}\left(N\right),\; \operatorname{SameAcross}\left(W, c, d\right) \Leftrightarrow \left(c.1 = d.1 \land \left(\forall j \in \operatorname{Fin}\left(N\right),\; \operatorname{min}\left(c.2, d.2\right) \le j \Rightarrow \left(j \le \operatorname{max}\left(c.2, d.2\right) \Rightarrow (c.1, j) \in W\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.SameAcross` (`✓ std3`).

*Citation.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Two cells share an across word when their rows agree and the inclusive horizontal interval is white.

**Definition 1.3 (Common down word).**

$$\forall N \in \mathrm{Nat},\; \forall W \in \operatorname{Finset}\left(\operatorname{Cell}\left(N\right)\right),\; \forall c \in \operatorname{Cell}\left(N\right),\; \forall d \in \operatorname{Cell}\left(N\right),\; \operatorname{SameDown}\left(W, c, d\right) \Leftrightarrow \left(c.2 = d.2 \land \left(\forall j \in \operatorname{Fin}\left(N\right),\; \operatorname{min}\left(c.1, d.1\right) \le j \Rightarrow \left(j \le \operatorname{max}\left(c.1, d.1\right) \Rightarrow (j, c.2) \in W\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.SameDown` (`✓ std3`).

*Citation.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Two cells share a down word when their columns agree and the inclusive vertical interval is white.

**Definition 1.4 (Complete rook placement).**

$$\forall N \in \mathrm{Nat},\; \forall W \in \operatorname{Finset}\left(\operatorname{Cell}\left(N\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{Cell}\left(N\right)\right),\; \operatorname{IsRookPlacement}\left(W, R\right) \Leftrightarrow \left(R \subseteq W \land \left(\left(\forall c \in \operatorname{Cell}\left(N\right),\; c \in R \Rightarrow \left(\forall d \in \operatorname{Cell}\left(N\right),\; d \in R \Rightarrow \left(c \ne d \Rightarrow \left(\left(\neg \operatorname{SameAcross}\left(W, c, d\right)\right) \land \left(\neg \operatorname{SameDown}\left(W, c, d\right)\right)\right)\right)\right)\right) \land \left(\forall c \in \operatorname{Cell}\left(N\right),\; c \in W \Rightarrow \left(\left(\exists d \in \operatorname{Cell}\left(N\right),\; d \in R \land \operatorname{SameAcross}\left(W, c, d\right)\right) \land \left(\exists d \in \operatorname{Cell}\left(N\right),\; d \in R \land \operatorname{SameDown}\left(W, c, d\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.IsRookPlacement` (`✓ std3`).

*Citation.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The rooks occupy white cells, no distinct pair shares a word, and every white cell shares each of its two words with a rook.

**Definition 1.5 (Rook-placement count).**

$$\forall N \in \mathrm{Nat},\; \forall W \in \operatorname{Finset}\left(\operatorname{Cell}\left(N\right)\right),\; \operatorname{rookCount}\left(W\right) = \operatorname{card}\left(\{ R \in \operatorname{powerset}\left(W\right) | \operatorname{IsRookPlacement}\left(W, R\right)\} \right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.rookCount` (`✓ std3`).

*Citation.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Count the subsets of the white cells that are complete rook placements.

**Definition 1.6 (Every natural count occurs).**

$$claim \Leftrightarrow \left(\forall r \in \mathrm{Nat},\; \exists N \in \mathrm{Nat},\; \exists W \in \operatorname{Finset}\left(\operatorname{Cell}\left(N\right)\right),\; \operatorname{rookCount}\left(W\right) = r\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.claim` (`✓ std3`).

*Citation.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Every natural number is the complete rook-placement count of some square crossword grid.

**Definition 1.7 (Square side length).**

$$\forall r \in \mathrm{Nat},\; \operatorname{gridSize}\left(r\right) = \operatorname{max}\left(5, 2 \cdot r - 1\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.gridSize` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The side length accommodates five columns and the first two r minus one rows, using subtraction in Nat.

**Definition 1.8 (Alternating side column).**

$$\forall i \in \mathrm{Nat},\; \operatorname{side}\left(i\right) = \operatorname{if}\left(i \bmod 2 = 0, 3, 1\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.side` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The side column is three for an even block index and one for an odd block index.

**Definition 1.9 (Alternating outer column).**

$$\forall i \in \mathrm{Nat},\; \operatorname{tip}\left(i\right) = \operatorname{if}\left(i \bmod 2 = 0, 4, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.tip` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The outer column is four for an even block index and zero for an odd block index.

**Definition 1.10 (Left row endpoint).**

$$\forall r \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \operatorname{rowLeft}\left(r, a\right) = \operatorname{if}\left(a \bmod 2 = 1, \operatorname{if}\left(a \bmod 4 = 1, 2, 0\right), \operatorname{if}\left(a = 0 \lor \left(a = 2 \cdot r - 2 \land a \bmod 4 = 2\right), 2, 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.rowLeft` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The left endpoint depends on row parity, its residue modulo four, and the two boundary rows.

**Definition 1.11 (Right row endpoint).**

$$\forall r \in \mathrm{Nat},\; \forall a \in \mathrm{Nat},\; \operatorname{rowRight}\left(r, a\right) = \operatorname{if}\left(a \bmod 2 = 1, \operatorname{if}\left(a \bmod 4 = 1, 4, 2\right), \operatorname{if}\left(a = 2 \cdot r - 2 \land a \bmod 4 = 0, 2, 3\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.rowRight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The right endpoint depends on row parity and the last even row.

**Definition 1.12 (White-cell family).**

$$\forall r \in \mathrm{Nat},\; \operatorname{white}\left(r\right) = \{ c \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right) | \operatorname{val}\left(c.1\right) < 2 \cdot r - 1 \land \left(\operatorname{rowLeft}\left(r, \operatorname{val}\left(c.1\right)\right) \le \operatorname{val}\left(c.2\right) \land \operatorname{val}\left(c.2\right) \le \operatorname{rowRight}\left(r, \operatorname{val}\left(c.1\right)\right)\right)\} $$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.white` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

The occupied rows contain exactly the cells between their inclusive row endpoints.

**Definition 1.13 (Placement with central index k).**

$$\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{candidate}\left(r, k\right) = \{ c \in \operatorname{Cell}\left(\operatorname{gridSize}\left(r\right)\right) | \left(\operatorname{val}\left(c.1\right) = 2 \cdot k \land \operatorname{val}\left(c.2\right) = 2\right) \lor \left(\left(\exists i \in \mathrm{Nat},\; i + 1 < r \land \left(\operatorname{val}\left(c.1\right) = 2 \cdot i + 1 \land \operatorname{val}\left(c.2\right) = \operatorname{tip}\left(i\right)\right)\right) \lor \left(\exists i \in \mathrm{Nat},\; i + 1 < r \land \left(\operatorname{val}\left(c.2\right) = \operatorname{side}\left(i\right) \land \left(\left(i < k \land \operatorname{val}\left(c.1\right) = 2 \cdot i\right) \lor \left(k \le i \land \operatorname{val}\left(c.1\right) = 2 \cdot i + 2\right)\right)\right)\right)\right)\} $$

*Formalization.* `D5/S3/Combinatorics/CrosswordRookCountsDefs.candidate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joel Brewster Lewis, Robert Won (2026). *Non-attacking rook placements on crossword grids*. DOI: [10.48550/arXiv.2609.03081](https://doi.org/10.48550/arXiv.2609.03081). URL: <https://arxiv.org/abs/2609.03081v1>.

*Commentary.*

Choose the central cell in row two k, every outer tip, and the top side endpoint before k or the bottom side endpoint from k onward.

## References

- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.Cell`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.IsRookPlacement`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.SameAcross`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.SameDown`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.candidate`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.gridSize`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.rookCount`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.rowLeft`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.rowRight`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.side`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.tip`
- Truth anchor: `D5/S3/Combinatorics/CrosswordRookCountsDefs.white`
