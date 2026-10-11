---
bibkey: paczosetal2021sudoq
authors: J. Paczos, M. Wierzbiński, G. Rajchel-Mieldzioć, A. Burchardt, K. Życzkowski
year: 2021
title: "Genuinely quantum SudoQ and its cardinality"
doi: 10.1103/PhysRevA.104.042423
url: https://arxiv.org/abs/2106.02967v2
claim: "Section III.A conjectures that no 4×4 SudoQ with three clues is uniquely solvable; Theorem 13 gives uniquely solvable grids with four clues."
strata_touched:
  - D5/S3/Quantum/LatinSquares/SudoQClueGeometry
  - D5/S3/Quantum/LatinSquares/SudoQMinimumClues
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1103/PhysRevA.104.042423

Source: https://arxiv.org/abs/2106.02967v2

Published as “Genuinely quantum solutions of the game Sudoku and their
cardinality”, Physical Review A 104 (2021), 042423.

## Source statements

Page numbers refer to arXiv:2106.02967v2.

Definition 2, p. 2:

> A quantum Latin square (QLS) is an $N\times N$ array of vectors from $N$-dimensional Hilbert space $\mathcal{H}_N$, arranged in such a way that each row and column forms an orthonormal basis of $\mathcal{H}_N$.

Definition 7, p. 3:

> A quantum Sudoku (SudoQ) is an $N^2 \times N^2$ QLS with additional constraints that each of the disjoint blocks of size $N$ forms an orthonormal basis.

Definition 8, p. 3:

> A quantum grid is a SudoQ grid whose some entries can be blank.

Definition 9, p. 3:

> A quantum grid is called solvable if it has at least one solution.

Definition 10, p. 3:

> A quantum grid is called uniquely solvable if it has a unique solution.

Definition 5, p. 2:

> The cardinality c of a QLS is the number of its vectors distinct up to a global phase.

Section III.A, p. 4:

> **Conjecture.** Similarly to the classical Sudoku there are no 4×4 SudoQ with 3 clues that are uniquely solvable.

Theorem 13, p. 4, gives a uniquely solvable four-clue grid for every 4×4 quantum
square of cardinality 16; its displayed clues are e1, f3, v2 and u4 at the four
positions (1,1), (2,3), (3,2) and (4,4), using the paper's one-based indices.

G. Rajchel-Mieldzioć, *Quantum mappings and designs*,
https://arxiv.org/abs/2204.13008, Chapter 7, restates the conjecture:

> Uniquely solvable grids of 4 × 4 SudoQ admit at least 4 clues.

## Encoding

The specialization is N = 2. Vectors are EuclideanSpace ℂ (Fin 4).
Rows and columns use zero-based Fin 4 indices. Blocks have indices
b : Fin 2 × Fin 2 and offsets k : Fin 2 × Fin 2, with cell
(2b.1 + k.1, 2b.2 + k.2). Four orthonormal vectors span the four-dimensional
space. A finite set C marks the nonblank entries, with literal prescribed
vectors v on C; values away from C impose no constraints. Solutions are
compared entry by entry up to a unit complex phase, as rays. Existence of a
solution is part of unique solvability. The statement with at most three clues
implies the paper's statement with exactly three.

## Mathematical consequence and boundary

The lower bound, together with the source's Theorem 13, gives an exact minimum
of four clues for uniquely solvable 4×4 SudoQ. The proof uses clue-fixing
reflection and basis swaps, followed by ray normalization and a four-cell
trade avoiding the clues. It includes unsolvable grids and arbitrary complex
clue vectors. The source's cardinality classification and four-clue
construction are unaffected. The minimum number of clues for 9×9 SudoQ is open.

The finite experiment is
[check.py](https://github.com/the-omega-institute/trureturing-experiments/blob/70eb46c96611a26464b7f8ea3330a67ffce8a605/docs/reports/paczos-et-al-2021-sudoq-three-clues/check.py),
sha256 e37ab13c1f3122f7063ceed89cb700c075970ebf88d9bdb23624fdb5476a83d8.
Its reported command is `python3 check.py`, exit 0, final reading `bad= 0`.
This computed check is separate from the Lean proof.

## Literature boundary

No earlier settlement was located in the inspected arXiv works and citation
abstracts. The PRA full text and the publisher full
text of DOI 10.1002/qute.70293 were not verified. Coverage of unindexed later
publications is ASSUMED-UNVERIFIED; absence of an earlier settlement is not a
kernel claim.
