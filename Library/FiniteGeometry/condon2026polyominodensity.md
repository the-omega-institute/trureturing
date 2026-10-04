---
bibkey: condon2026polyominodensity
authors: D. M. Condon, E. B. Dugan, L. M. Goldman, E. R. Williams
year: 2026
title: "Polyomino Density"
doi: 10.48550/arXiv.2608.29231
url: https://arxiv.org/abs/2608.29231v1
claim: "The instance sequence for the L n-omino is S(n, 1, 2) in general (Section 6.3)."
strata_touched:
  - D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence
license: citation-only
triage: anchor
---

# Polyomino density and skipped-number sequences

## Locator

DOI: 10.48550/arXiv.2608.29231.
Versioned source: https://arxiv.org/abs/2608.29231v1.

The source is arXiv:2608.29231v1. Its Section 6.3, p. 28, says:

> We believe S(5, 1, 2) is the same as the instance sequence for [L pentomino], and we suspect that the instance sequence for the L n-omino is S(n, 1, 2) in general.

The bracketed label denotes the source's inline L pentomino diagram.

Section 1, printed p. 1:

> A polyomino is a connected shape made from unit squares, called cells, glued together edge-to-edge.

Section 1, printed p. 3:

> For N any positive integer, if P is a polyomino of minimum size among those polyominoes containing at least N instances (translated copies) of some polyomino p, we say that P is (p, N)-dense

> We let a_{p,N} denote the size of a (p, N)-dense polyomino, and we call (a_{p,N})_{N=1}^∞ the instance sequence for p.

Section 2.1, p. 4:

> In this paper, we deal with fixed polyominoes, meaning we consider two polyominoes to be the same shape if they differ by translation only; we call these two instances of that shape.

> We regard the cells of all polyominoes as orthogonal unit squares on the Cartesian plane, with their lower left corners having integer coordinates.

Section 4.4, p. 15:

> We define an L n-omino, for n ≥ 3, to be a left-aligned polyomino with two rows that has 1 cell in the top row and n − 1 cells in the bottom row.

Section 6.3, p. 28:

> In a recent preprint [Clo25], Benoit Cloitre defines an S(x, y, z) sequence to be an increasing sequence of integers a_k starting with a_1 = x, such that for k > 1, a_k − a_{k−1} = y if k occurs in the sequence before position k, and otherwise a_k − a_{k−1} = z.

[Clo25] is Benoit Cloitre, *A study of self-referential sequences*,
arXiv:2506.18103v2. Theorems 5.1–5.3 concern x = 3, 4, 5.

Theorem 4.9 of *Polyomino Density* gives a closed form for the L instance
minimum. The Lean result identifies that minimum with the independent
S(n,1,2) recursion for every n ≥ 3 and positive N. Its geometric lower bound
holds for arbitrary finite cell sets, including disconnected sets. Trimmed
down-sets attain it and provide connected minimizers. Integer cells and their
edge-gluing relation use the frozen `OrderedGridMemory.Point` carrier and
`SquareGridCoordinates.squareGrid.Adj` four-neighbor graph directly.

Prior-resolution evidence is bounded by the searches recorded in issue
12562. Later citing works were not exhaustively checked: the citation service
returned a rate-limit response. No priority claim follows from that negative
search finding.
