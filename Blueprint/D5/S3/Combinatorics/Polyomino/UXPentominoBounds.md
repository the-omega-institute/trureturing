# The U and X Pentomino Instance Sequences

## Abstract

At every positive threshold the fewest board cells needed for U and X pentomino translates agree.

Section 10 of Condon, Dugan, Goldman and Williams poses the equality for finite nonempty square-grid boards connected by horizontal and vertical unit edges. The minimum counts all distinct translation anchors and requires at least N of them. Both sides use the board, translation, and minimum definitions from LPolyominoSkippedSequence.

**Definition 1.1 (The U pentomino).**

$$U = \left\{(- 1, 0), (0, 0), (1, 0), (- 1, 1), (1, 1)\right\}$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.U` (`✓ std3`).

*Citation.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The origin is the middle cell of the bottom row.

**Definition 1.2 (The X pentomino).**

$$X = \left\{(0, 0), (- 1, 0), (1, 0), (0, - 1), (0, 1)\right\}$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.X` (`✓ std3`).

*Citation.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The origin is the center of the cross.

**Theorem 1.3 (The U board lower bound).**

$$\forall (P : \operatorname{Finset}\left(Point\right)), (0 < \operatorname{card}\left(\operatorname{instances}\left(P, U\right)\right)) \Rightarrow ((\operatorname{card}\left(\operatorname{instances}\left(P, U\right)\right) + 2 \le \operatorname{card}\left(P\right)) \land (8 \cdot \operatorname{card}\left(\operatorname{instances}\left(P, U\right)\right) \le (\operatorname{card}\left(P\right) - \operatorname{card}\left(\operatorname{instances}\left(P, U\right)\right) - 2)^{2} + 4))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.u_card_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Each nonempty anchor column supplies an extra cell in either outer arm column. In each parity, send columns to the arm directed away from a maximum and keep both arms of that maximum. This counts disjoint columns even for profiles with gaps. The two parity counts and the center-cell constraint give the quadratic bound.

**Theorem 1.4 (The X board lower bound).**

$$\forall (P : \operatorname{Finset}\left(Point\right)), (0 < \operatorname{card}\left(\operatorname{instances}\left(P, X\right)\right)) \Rightarrow ((\operatorname{card}\left(\operatorname{instances}\left(P, X\right)\right) + 2 \le \operatorname{card}\left(P\right)) \land (8 \cdot \operatorname{card}\left(\operatorname{instances}\left(P, X\right)\right) \le (\operatorname{card}\left(P\right) - \operatorname{card}\left(\operatorname{instances}\left(P, X\right)\right) - 2)^{2} + 4))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.x_card_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Condon, Dugan, Goldman and Williams derive the X optimum in Section 5 and state its explicit formula in Theorem 6.4. The finite-set bound here uses the center and two vertical arms in integer coordinates (x + y, y).

**Theorem 1.5 (Compressing X boards to U boards).**

$$\forall (P : \operatorname{Finset}\left(Point\right)), (\operatorname{IsPolyomino}\left(P\right)) \Rightarrow (\exists (Q : \operatorname{Finset}\left(Point\right)), (\operatorname{IsPolyomino}\left(Q\right)) \land ((\operatorname{card}\left(\operatorname{instances}\left(P, X\right)\right) \le \operatorname{card}\left(\operatorname{instances}\left(Q, U\right)\right)) \land (\operatorname{card}\left(Q\right) = \operatorname{card}\left(P\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.u_board_of_x_board` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Section 3, Lemmas 3.1–3.3 and Figure 8 of the cited paper give the comparison that the U minimum is at most the X minimum. Here each diagonal column is stacked at height zero while preserving its cardinality. An original board edge changes x + y by one, so original paths give paths along the new bottom row. Stacking the translation-anchor fibers fits every U arm by the same column bound.

**Theorem 1.6 (Equality for every positive threshold).**

$$\forall (N : \mathbb{N}), (0 < N) \Rightarrow (\operatorname{a}\left(U, N\right) = \operatorname{a}\left(X, N\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.same_minimum` (`✓ std3`). ∎

*Resolves.* `Problems/condon-dugan-goldman-williams-2026-ux-pentomino-instance-sequence` (proved) by `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.same_minimum`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"condon-dugan-goldman-williams-2026-ux-pentomino-instance-sequence","declaration_gid":"D5/S3/Combinatorics/Polyomino/UXPentominoBounds.same_minimum","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The reverse U lower bound supplies the missing inequality in the Section 10 conjecture. It bounds the slack above N + 2. In coordinates (x + y, x − y), a balanced checkerboard rectangle realizes the corresponding anchor capacity. Trim a suffix of its last anchor row and delete the associated cells of the outer board row. Each deleted outer cell could only support deleted anchors. The full lower rows connect the resulting X board. The area-preserving transfer gives the Section 3 comparison.

## References

- Truth anchor: `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.U`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.X`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.same_minimum`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.u_board_of_x_board`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.u_card_bound`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/UXPentominoBounds.x_card_bound`
- Dependency: [D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence](LPolyominoSkippedSequence.md)
