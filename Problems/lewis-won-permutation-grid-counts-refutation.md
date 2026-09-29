---
slug: lewis-won-permutation-grid-counts-refutation
bibkey: lewis2026crossword
doi: 10.48550/arXiv.2609.03081
url: https://arxiv.org/abs/2609.03081v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CrosswordPermutationGridRefutation.result
---

# A Permutation Grid with 155 Rook Placements

## Problem

Joel Brewster Lewis and Robert Won, *Non-attacking rook placements on crossword grids*, arXiv:2609.03081v1, Section 3.3:

> Conjecture 3.10. A positive integer r occurs as the rook placement count of a permutation grid if and only if r ≠ 4, r ≠ 12, and
> r ≢ 3 (mod 4).

The paper supports the conjecture by exhaustive computation over permutations with `n ≤ 8`, recorded for the counts `r ≤ 108`.

## Motivation

The frozen theorem `D5/S3/Combinatorics/CrosswordPermutationGridRefutation.result` refutes the conjecture. The module also proves, for any
grid with a certified list of its words, that complete rook placements are exactly the perfect matchings of the word-intersection graph
and that a recursive matching count equals the rook count.

## Gap

Issue 10091 records the screen made before the work: the arXiv record has only v1, and no citing paper, public review page, searched
formal-conjecture catalogue or repository file revisits the conjecture.

## Route

1. For every grid given with a list of across words partitioning its white cells and a labelling of its down words, placements are the
   perfect matchings of the word graph.
2. A recursion over the across words, rejecting reused down words, counts these matchings and equals the rook count.
3. For the permutation `2 7 4 8 1 6 3 5` the grid has 14 across and 14 down words, and the recursion evaluates to 155 in the kernel.
4. Since `155 ≡ 3 (mod 4)`, the forward direction of the conjecture fails.

## Falsifier

The statement would fail if the computed word lists did not coincide with the maximal runs of the grid, or if the grid had a number of
placements other than 155.

## Evidence

Exhaustive enumeration of all permutations with `n ≤ 8`: no counterexample for `n ≤ 7`; for `n = 8` exactly 32 permutations violate the
conjecture, with counts 155 (24 permutations), 191 (4) and 195 (4). The value 155 was recomputed by three independent programs, one of
them the Ryser permanent of the 14 × 14 word-intersection matrix; the counting convention reproduces the paper's values `263154 ↦ 5`,
`25143 ↦ 6` and the maxima `1, 1, 1, 5, 17, 73, 469` for `n ≤ 7`.

## Triage

`theorem`; Tier 1 conjecture stated in a 2026 paper, preregistered in issue 10091 before the work. The concrete count is a certified
instance used only to refute the named conjecture.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources named above; no worldwide priority claim is made.
