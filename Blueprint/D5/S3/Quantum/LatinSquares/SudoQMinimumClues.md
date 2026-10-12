# Four clues are necessary for unique SudoQ solvability

## Abstract

No uniquely solvable four by four SudoQ has at most three clues.

**Definition 1.1 (The three-clue conjecture).**

$$claim = \left(\forall C \in \operatorname{Finset}\left(\operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right)\right),\; \forall v \in \operatorname{Fin}\left(4\right) \times \operatorname{Fin}\left(4\right) \to \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(4\right)\right),\; \operatorname{Finset}.\operatorname{card} C \le 3 \Rightarrow \left(\neg \operatorname{UniquelySolvable}\left(C, v\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/LatinSquares/SudoQMinimumClues.claim` (`✓ std3`).

*Citation.* J. Paczos, M. Wierzbiński, G. Rajchel-Mieldzioć, A. Burchardt, K. Życzkowski (2021). *Genuinely quantum SudoQ and its cardinality*. DOI: [10.1103/PhysRevA.104.042423](https://doi.org/10.1103/PhysRevA.104.042423). URL: <https://arxiv.org/abs/2106.02967v2>.

*Commentary.*

Section III.A, page 4: “Similarly to the classical Sudoku there are no 4×4 SudoQ with 3 clues that are uniquely solvable.” The thesis Quantum mappings and designs, Chapter 7, restates it as “Uniquely solvable grids of 4 × 4 SudoQ admit at least 4 clues.” C is the finite set of nonblank cells and v assigns their literal complex vectors. Coordinates start at zero. The at-most-three statement includes zero, one and two clues as well as three. Unique solvability includes existence and compares completions entry by entry as rays.

**Theorem 1.2 (At most three clues never suffice).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/LatinSquares/SudoQMinimumClues.result` (`✓ std3`). ∎

*Resolves.* `Problems/paczos-et-al-2021-sudoq-three-clues` (proved) by `D5/S3/Quantum/LatinSquares/SudoQMinimumClues.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"paczos-et-al-2021-sudoq-three-clues","declaration_gid":"D5/S3/Quantum/LatinSquares/SudoQMinimumClues.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. Paczos, M. Wierzbiński, G. Rajchel-Mieldzioć, A. Burchardt, K. Życzkowski (2021). *Genuinely quantum SudoQ and its cardinality*. DOI: [10.1103/PhysRevA.104.042423](https://doi.org/10.1103/PhysRevA.104.042423). URL: <https://arxiv.org/abs/2106.02967v2>.

*Commentary.*

Suppose a solution were unique. The clue geometry then forces a repeated ray in every row, column and block. Sudoku-preserving row and column permutations put its four positions in a fixed pattern. Orthogonality forces one of two normal forms, exchanged by transposition. In either form, four disjoint rectangles partition the cells, and each supports a swap of two orthogonal rays. Three clues miss a rectangle. Its swap gives a second solution with a changed ray. Cells outside the rectangle retain their original vectors literally, so every prescribed clue is preserved. The argument applies to arbitrary clue vectors and also excludes unique solvability when there is no completion.

## References

- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQMinimumClues.claim`
- Truth anchor: `D5/S3/Quantum/LatinSquares/SudoQMinimumClues.result`
- Dependency: [D5/S3/Quantum/LatinSquares/SudoQClueGeometry](SudoQClueGeometry.md)
