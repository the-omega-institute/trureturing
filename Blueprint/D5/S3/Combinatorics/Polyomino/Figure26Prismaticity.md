# Prismatic polyhexes in Figure 26

## Abstract

Both binary-colored 28-cell boards in Figure 26 are prismatic.

Section 9.1 and Figure 26 concern fixed translates on the hexagonal lattice. The cell carrier Point is the integer pair type from OrderedGridMemory. The coordinate changes below preserve edge adjacency, including the color and position of each cell.

**Definition 1.1 (Axial edge steps).**

$$hexSteps = \{(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)\}$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.hexSteps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

An edge joins cells whose difference is one of these six steps.

**Definition 1.2 (Edge adjacency).**

$$\forall (p : Point), \forall (q : Point), (\operatorname{Adj}\left(p, q\right)) \Leftrightarrow (q - p \in hexSteps)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.Adj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The difference is computed componentwise on the integer pairs.

**Definition 1.3 (Paths within a board).**

$$\forall (B : \operatorname{Finset}\left(Point\right)), \forall (p : Point), \forall (q : Point), (\operatorname{BoardReach}\left(B, p, q\right)) \Leftrightarrow (\operatorname{ReflTransGen}\left((x : Point) \mapsto (y : Point) \mapsto (x \in B) \land ((y \in B) \land (\operatorname{Adj}\left(x, y\right))), p, q\right))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.BoardReach` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

ReflTransGen allows the length-zero path. Both endpoints of each edge of a positive-length path lie in the board.

**Definition 1.4 (Nonempty connected boards).**

$$\forall (B : \operatorname{Finset}\left(Point\right)), (\operatorname{IsPolyhex}\left(B\right)) \Leftrightarrow ((\operatorname{Nonempty}\left(B\right)) \land (\forall (p : Point), (p \in B) \Rightarrow (\forall (q : Point), (q \in B) \Rightarrow (\operatorname{BoardReach}\left(B, p, q\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.IsPolyhex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Every pair of cells in the nonempty board is joined by a path using its cells.

**Definition 1.5 (Cell set of an ordered glyph).**

$$\forall (P : \operatorname{Fin}\left(4\right) \Rightarrow Point), \operatorname{offsets}\left(P\right) = \operatorname{image}\left(P, univ\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.offsets` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

There are four ordered offsets. Its underlying set is the image of all four indices.

**Definition 1.6 (Fixed translates in a board).**

$$\forall (P : \operatorname{Fin}\left(4\right) \Rightarrow Point), \forall (B : \operatorname{Finset}\left(Point\right)), \operatorname{anchors}\left(P, B\right) = \operatorname{filter}\left((t : Point) \mapsto \forall (i : \operatorname{Fin}\left(4\right)), t + \operatorname{P}\left(i\right) \in B, \operatorname{image}\left((x : Point) \mapsto x - \operatorname{P}\left(0\right), B\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.anchors` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

An anchor is a translation vector whose copy lies entirely in the board. Index zero supplies the finite candidate set. Two distinct vectors give distinct cell sets since a nonempty finite subset of the integer lattice has no nonzero translation period. Different copies may overlap.

**Definition 1.7 (Minimum area for at least a given number of translates).**

$$\forall (P : \operatorname{Fin}\left(4\right) \Rightarrow Point), \forall (N : \mathbb{N}), \forall (B : \operatorname{Finset}\left(Point\right)), (\operatorname{IsDense}\left(P, N, B\right)) \Leftrightarrow ((\operatorname{IsPolyhex}\left(B\right)) \land ((N \le \operatorname{card}\left(\operatorname{anchors}\left(P, B\right)\right)) \land (\forall (C : \operatorname{Finset}\left(Point\right)), (\operatorname{IsPolyhex}\left(C\right)) \Rightarrow ((N \le \operatorname{card}\left(\operatorname{anchors}\left(P, C\right)\right)) \Rightarrow (\operatorname{card}\left(B\right) \le \operatorname{card}\left(C\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.IsDense` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Area is the number of cells. The comparison ranges over all finite nonempty connected boards meeting the count.

**Definition 1.8 (Four binary entries).**

$$Word = Bool \times (Bool \times (Bool \times Bool))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.Word` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The product is right-associated in Lean.

**Definition 1.9 (Word read at an anchor).**

$$\forall (P : \operatorname{Fin}\left(4\right) \Rightarrow Point), \forall (c : Point \Rightarrow Bool), \forall (t : Point), \operatorname{wordAt}\left(P, c, t\right) = (\operatorname{c}\left(t + \operatorname{P}\left(0\right)\right), \operatorname{c}\left(t + \operatorname{P}\left(1\right)\right), \operatorname{c}\left(t + \operatorname{P}\left(2\right)\right), \operatorname{c}\left(t + \operatorname{P}\left(3\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.wordAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The four positions follow the displayed glyph in the recorded order. True denotes gray and false denotes white.

**Definition 1.10 (Each word appears once).**

$$\forall (P : \operatorname{Fin}\left(4\right) \Rightarrow Point), \forall (B : \operatorname{Finset}\left(Point\right)), \forall (c : Point \Rightarrow Bool), (\operatorname{IsBinaryDeBruijn}\left(P, B, c\right)) \Leftrightarrow (\forall (w : Word), \operatorname{card}\left(\operatorname{filter}\left((t : Point) \mapsto \operatorname{wordAt}\left(P, c, t\right) = w, \operatorname{anchors}\left(P, B\right)\right)\right) = 1)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.IsBinaryDeBruijn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

For every word in the fourfold product the exact multiplicity is one.

**Definition 1.11 (The data certified for each panel).**

$$\forall (P : \operatorname{Fin}\left(4\right) \Rightarrow Point), \forall (B : \operatorname{Finset}\left(Point\right)), \forall (c : Point \Rightarrow Bool), (\operatorname{FigureWitness}\left(P, B, c\right)) \Leftrightarrow ((\operatorname{IsPolyhex}\left(\operatorname{offsets}\left(P\right)\right)) \land ((\operatorname{card}\left(\operatorname{offsets}\left(P\right)\right) = 4) \land ((\operatorname{IsPolyhex}\left(B\right)) \land ((\operatorname{card}\left(B\right) = 28) \land ((\operatorname{card}\left(\operatorname{anchors}\left(P, B\right)\right) = 16) \land (\operatorname{IsBinaryDeBruijn}\left(P, B, c\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.FigureWitness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The connected glyph has four distinct cells. The connected board has 28 cells and exactly 16 anchors.

**Definition 1.12 (Prismaticity for these Figure 26 panels).**

$$\forall (P : \operatorname{Fin}\left(4\right) \Rightarrow Point), \forall (B : \operatorname{Finset}\left(Point\right)), \forall (c : Point \Rightarrow Bool), (\operatorname{IsPrismatic}\left(P, B, c\right)) \Leftrightarrow ((\operatorname{FigureWitness}\left(P, B, c\right)) \land (\operatorname{IsDense}\left(P, 16, B\right)))$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.IsPrismatic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

In this Figure 26 model prismaticity requires the displayed witness and density at 16 translates.

**Definition 1.13 (Left glyph in issue coordinates).**

$$leftIssuePattern = [(0, -1), (0, 0), (1, 0), (-1, 1)]$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.leftIssuePattern` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The vector lists the values at indices zero through three in order.

**Definition 1.14 (Left board in issue coordinates).**

$$leftIssueBoard = \{(-6, 2), (-6, 3), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0)\}$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.leftIssueBoard` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The source cells are sent to the issue axes by (q,r) ↦ (−q,−r).

**Definition 1.15 (Left gray-cell indicator).**

$$\forall (p : Point), \operatorname{leftIssueColor}\left(p\right) = \operatorname{decide}\left(p \in \{(-6, 2), (-5, 0), (-5, 3), (-4, -2), (-4, -1), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 1), (-1, -2), (-1, 0)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.leftIssueColor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The gray coordinate set is the image of the gray centers under the same board map.

**Definition 1.16 (Right glyph in issue coordinates).**

$$rightIssuePattern = [(0, 0), (1, 0), (-1, 1), (1, 1)]$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.rightIssuePattern` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The vector lists the values at indices zero through three in order.

**Definition 1.17 (Right board in issue coordinates).**

$$rightIssueBoard = \{(-7, 0), (-6, -1), (-6, 0), (-5, -2), (-5, -1), (-5, 0), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0)\}$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.rightIssueBoard` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The source cells are sent to the issue axes by (q,r) ↦ (−r,−q).

**Definition 1.18 (Right gray-cell indicator).**

$$\forall (p : Point), \operatorname{rightIssueColor}\left(p\right) = \operatorname{decide}\left(p \in \{(-6, -1), (-5, -2), (-4, -2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-2, -1), (-1, -2), (-1, 0), (0, -2), (0, -1)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.rightIssueColor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

The board map sends the gray centers to this coordinate set. The right glyph alone is additionally shifted by (1,1), with the translate anchor shifted back accordingly.

**Theorem 1.19 (Left panel prismaticity).**

$$((\operatorname{IsPolyhex}\left(\operatorname{offsets}\left(leftIssuePattern\right)\right)) \land ((\operatorname{card}\left(\operatorname{offsets}\left(leftIssuePattern\right)\right) = 4) \land ((\operatorname{IsPolyhex}\left(leftIssueBoard\right)) \land ((\operatorname{card}\left(leftIssueBoard\right) = 28) \land ((\operatorname{card}\left(\operatorname{anchors}\left(leftIssuePattern, leftIssueBoard\right)\right) = 16) \land (\forall (w : Word), \operatorname{card}\left(\operatorname{filter}\left((t : Point) \mapsto \operatorname{wordAt}\left(leftIssuePattern, leftIssueColor, t\right) = w, \operatorname{anchors}\left(leftIssuePattern, leftIssueBoard\right)\right)\right) = 1)))))) \land (\operatorname{IsDense}\left(leftIssuePattern, 16, leftIssueBoard\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.left_issue_prismatic` (`✓ std3`). ∎

*Resolves.* `Problems/condon-dugan-goldman-williams-2026-figure-26-left-prismaticity` (proved) by `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.left_issue_prismatic`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"condon-dugan-goldman-williams-2026-figure-26-left-prismaticity","declaration_gid":"D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.left_issue_prismatic","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Choose 16 distinct anchors in a competing board. The center and the three arm offsets lie in two residues of the index-three lattice kernel. Within each relevant residue, the arms form a simplex. If m input points have growth g, the occupied rows and their vertical endpoints give 2m ≤ g(g−1). Each output residue receives both centers and the preceding residue’s expanded arms. A finite check of the three residue counts summing to 16 forces at least 28 cells. The exhibited board has 28 cells and its 16 words occur exactly once.

**Theorem 1.20 (Right panel prismaticity).**

$$((\operatorname{IsPolyhex}\left(\operatorname{offsets}\left(rightIssuePattern\right)\right)) \land ((\operatorname{card}\left(\operatorname{offsets}\left(rightIssuePattern\right)\right) = 4) \land ((\operatorname{IsPolyhex}\left(rightIssueBoard\right)) \land ((\operatorname{card}\left(rightIssueBoard\right) = 28) \land ((\operatorname{card}\left(\operatorname{anchors}\left(rightIssuePattern, rightIssueBoard\right)\right) = 16) \land (\forall (w : Word), \operatorname{card}\left(\operatorname{filter}\left((t : Point) \mapsto \operatorname{wordAt}\left(rightIssuePattern, rightIssueColor, t\right) = w, \operatorname{anchors}\left(rightIssuePattern, rightIssueBoard\right)\right)\right) = 1)))))) \land (\operatorname{IsDense}\left(rightIssuePattern, 16, rightIssueBoard\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.right_issue_prismatic` (`✓ std3`). ∎

*Resolves.* `Problems/condon-dugan-goldman-williams-2026-figure-26-right-prismaticity` (proved) by `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.right_issue_prismatic`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"condon-dugan-goldman-williams-2026-figure-26-right-prismaticity","declaration_gid":"D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.right_issue_prismatic","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams (2026). *Polyomino Density*. DOI: [10.48550/arXiv.2608.29231](https://doi.org/10.48550/arXiv.2608.29231). URL: <https://arxiv.org/abs/2608.29231v1>.

*Commentary.*

Choose 16 distinct anchors in a competing board. Each output column is the union of its own input column expanded by vertical offsets 0 and 2 and the preceding input column expanded by 0 and 1. Parity supplies the interior gain and the tight first-column bound. If a consecutive run has excess E at most 11, its at most five columns give an anchor count at most 47E/33. Runs separated by missing input columns have disjoint output supports. Thus excess at most 11 would allow fewer than 16 anchors. The exhibited board has 28 cells and its 16 words occur exactly once.

## References

- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.Adj`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.BoardReach`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.FigureWitness`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.IsBinaryDeBruijn`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.IsDense`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.IsPolyhex`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.IsPrismatic`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.Word`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.anchors`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.hexSteps`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.leftIssueBoard`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.leftIssueColor`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.leftIssuePattern`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.left_issue_prismatic`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.offsets`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.rightIssueBoard`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.rightIssueColor`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.rightIssuePattern`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.right_issue_prismatic`
- Truth anchor: `D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.wordAt`
