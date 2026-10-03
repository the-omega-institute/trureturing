---
slug: lewis-won-skew-merged-rook-placements
bibkey: lewis2026crossword
doi: 10.48550/arXiv.2609.03081
url: https://arxiv.org/abs/2609.03081v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CrosswordGrid/SkewMergedRook.result
---

# Skew-Merged Permutations Are Exactly Those With One or Two Rook Placements

## Problem

Joel Brewster Lewis and Robert Won, *Non-attacking rook placements on crossword grids*, arXiv:2609.03081v1, Section 3.3:

> Conjecture 3.9. A permutation w ∈ S_n is skew-merged if and only if Grid(w) admits exactly one or two rook placements.

Grid(w) is the n × n board whose black squares are (i, w(i)); a rook placement is a set of white squares meeting every across word and every
down word exactly once. A permutation is skew-merged when its entries split into an increasing and a decreasing subsequence. The paper proves
the forward direction (Proposition 3.8) and characterizes exactly one placement (Theorem 3.7).

## Motivation

The theorem `D5/S3/Combinatorics/CrosswordGrid/SkewMergedRook.result` establishes the equivalence for every n ≥ 1 and every permutation of
[n].

## Gap

Pre-registration issue 12533 records the screen made before the work: the arXiv record has only v1, and web, GitHub and repository searches
found no proof of the reverse direction. This is a bounded negative finding.

## Route

1. Rook placements of a permutation grid are the perfect matchings of its word graph; every permutation grid has at least one.
2. Skew-merged permutations decompose into five regions, which forces one placement or exactly two.
3. Deleting an extreme entry (first, last, smallest or largest) injects the placements of the smaller grid into those of the larger one,
   so the placement count never decreases under these deletions; general pattern containment is not used, since it does not preserve
   the count (r(263154) = 5 < r(25143) = 6).
4. A permutation that is not skew-merged but all of whose extreme deletions are skew-merged belongs to a finite list of families; for each
   family three distinct placements are written down for every value of its parameters.
5. Strong induction on n combines the deletions with the families.

## Falsifier

The statement would fail if an extreme deletion could lose a placement, or if the classification of the boundary-minimal permutations missed
a family.

## Evidence

An independent referee implementation checked the theorem and every intermediate lemma exhaustively for all 4,037,913 permutations with
n ≤ 10, and the explicit families for all parameters up to 40.

## Triage

`theorem`; the statement is Conjecture 3.9 of arXiv:2609.03081v1, quantified over every n ≥ 1.

- Proved (formalized): a permutation grid has one or two rook placements exactly when the permutation is skew-merged.
- Proved (formalized): placement counts do not decrease when an extreme entry is deleted.
- Computed: the numbers of permutations of [n] with exactly one and exactly two placements are 12,870 and 7,648 for n = 9, and 48,620 and
  31,312 for n = 10; these agree with binom(2n − 2, n − 1) and with the paper's formula
  binom(2n, n) − binom(2n − 2, n − 1) − Σ_{m=0}^{n−1} 2^{n−m−1} binom(2m, m), which the paper derives from Conjecture 3.9.
- Open: a formalized derivation of that counting formula from the equivalence; Question 4.2's characterization of the grids with exactly r
  placements for r ≥ 3.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record, web and GitHub searches and the repository checks recorded above.
