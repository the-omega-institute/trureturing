---
slug: lewis-won-crossword-rook-counts
bibkey: lewis2026crossword
doi: 10.48550/arXiv.2609.03081
url: https://arxiv.org/abs/2609.03081v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CrosswordRookCounts.result
---

# Every Natural Number Counts the Rook Placements of a Crossword Grid

## Problem

Joel Brewster Lewis and Robert Won, *Non-attacking rook placements on crossword grids*, arXiv:2609.03081v1, Question 4.2:

> For which positive integers r does there exist a crossword grid which admits exactly r rook placements? Can the crossword grids which
> admit exactly r rook placements be characterized?

The paper observes that block-diagonal juxtaposition multiplies counts, so that it suffices to treat prime `r`, and it conjectures that
permutation grids miss infinitely many values.

## Motivation

The frozen theorem `D5/S3/Combinatorics/CrosswordRookCounts.result` shows that every natural number is attained by a square crossword grid.
This answers the first part of Question 4.2; the characterization asked in the second part is not addressed.

## Gap

Issue 10086 records the screen made before the work: the arXiv record has only v1, and neither citing papers, the paper's public review
page, the searched formal-conjecture catalogues nor this repository answer the question.

## Route

1. For `r ≥ 1` take the grid of side `max(5, 2r − 1)` whose white cells are the first `2r − 1` cells of column 2 together with, for
   `0 ≤ i ≤ r − 2`, the cells `(2i, s_i)`, `(2i + 1, s_i)`, `(2i + 2, s_i)`, `(2i + 1, t_i)`, where `(s_i, t_i) = (3, 4)` for even `i` and
   `(1, 0)` for odd `i`.
2. The cells `(2i + 1, t_i)` are down words of length one, so every placement contains them and no other cell of row `2i + 1`.
3. Hence column 2 carries exactly one rook, at some row `2k` with `k < r`, and the three-cell side words are then forced to their upper
   endpoint before block `k` and to their lower endpoint from block `k` on.
4. Each of these `r` forced choices is a placement, so the grid has exactly `r` placements.
5. For `r = 0`, the 3 × 3 grid with white cells `(0,1)`, `(0,2)`, `(1,0)`, `(2,0)` has two length-one down words inside one across word.

## Falsifier

The statement would fail if some grid of the family had a placement avoiding a length-one down word or more than one rook in column 2.

## Evidence

Exhaustive enumeration shows that `2 × 2`, `3 × 3` and `4 × 4` grids attain `{1, 2}`, `{0, 1, 2, 3, 4, 6}` and
`{0, …, 8, 10, 12, 14, 18, 24}`; the family was recounted independently for `1 ≤ r ≤ 120`.

## Triage

`theorem`; Tier 1 open question stated in a 2026 paper, preregistered in issue 10086 before the work. The computational use is `none`:
the central theorems hold for every `r`.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources named above; no worldwide priority claim is made.
