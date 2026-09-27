---
bibkey: lewis2026crossword
authors: Joel Brewster Lewis, Robert Won
year: 2026
title: "Non-attacking rook placements on crossword grids"
doi: 10.48550/arXiv.2609.03081
url: https://arxiv.org/abs/2609.03081v1
claim: "Question 4.2. For which positive integers r does there exist a crossword grid which admits exactly r rook placements? … Conjecture 3.10. A positive integer r occurs as the rook placement count of a permutation grid if and only if r ≠ 4, r ≠ 12, and r ≢ 3 (mod 4)."
strata_touched:
  - D5/S3/Combinatorics/CrosswordRookCountsDefs
  - D5/S3/Combinatorics/CrosswordRookCounts
  - D5/S3/Combinatorics/CrosswordPermutationGridRefutation
license: citation-only
triage: anchor
---

# Lewis and Won, rook placements on crossword grids

A crossword grid is an array of white and black squares; an across (down) word is a maximal run of white squares in a row (column). A
complete non-attacking rook placement is a set of white squares meeting every across word and every down word exactly once, equivalently
a perfect matching of the bipartite graph whose vertices are the words and whose edges are the white squares.

## Verified locator

DOI: 10.48550/arXiv.2609.03081

URL: https://arxiv.org/abs/2609.03081v1

The arXiv record shows only v1 (2 September 2026).

- Locator: Section 2, definitions of across and down words and of complete non-attacking rook placements, and the identification
  `|RP(G)| = perm(B_G)`.
- Locator: Section 3.3, "Exhaustive computer computation for n ≤ 8 shows that for all r ≤ 108 other than the values r = 4, 12, and all
  numbers congruent to 3 modulo 4, there exists a permutation w such that |RP(Grid(w))| = r. We therefore conjecture the following.
  Conjecture 3.10. A positive integer r occurs as the rook placement count of a permutation grid if and only if r ≠ 4, r ≠ 12, and
  r ≢ 3 (mod 4)."
- Locator: Section 4.2, "Question 4.2. For which positive integers r does there exist a crossword grid which admits exactly r rook
  placements? Can the crossword grids which admit exactly r rook placements be characterized?"

## Reading of the statements

Question 4.2 asks for the set of attained counts over all crossword grids. Conjecture 3.10 describes the attained counts over permutation
grids, the grids whose black squares form a permutation matrix.

## Scope of the recorded answers

Every natural number is the rook-placement count of some square crossword grid, which answers the first part of Question 4.2; the
characterization asked in its second part is not addressed. Conjecture 3.10 is false: the permutation grid of `2 7 4 8 1 6 3 5` has 155
placements and `155 ≡ 3 (mod 4)`.

## Bounded prior-resolution evidence

Read on 2026-09-26: the arXiv record (v1 only), a full-text arXiv search for crossword and rook (only this paper), the Pith review page of
the paper, google-deepmind/formal-conjectures and conjectures.io; none answers Question 4.2 or revisits Conjecture 3.10. This is a bounded
negative finding for a paper posted three weeks earlier.
