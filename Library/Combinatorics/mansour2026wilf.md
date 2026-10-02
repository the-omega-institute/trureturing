---
bibkey: mansour2026wilf
authors: Toufik Mansour
year: 2026
title: "Wilf Classes for Level Sequences Avoiding Patterns of Length Three"
doi: 10.3390/math14111983
url: https://www.mdpi.com/2227-7390/14/11/1983
claim: "Problem 1: level sequences avoiding 101 and 102 are counted by the Catalan numbers."
strata_touched:
  - D5/S3/Combinatorics/LevelSequence/LevelSequenceCatalan
license: citation-only
triage: anchor
---

# Mansour, Wilf classes for level sequences avoiding patterns of length three

The paper classifies level sequences avoiding one, two or three patterns of length three up to Wilf
equivalence and determines their generating functions, leaving one case as an open problem.

## Verified locator

DOI: 10.3390/math14111983

URL: https://www.mdpi.com/2227-7390/14/11/1983

- Locator: Section 1, lev(w) is the number of levels, that is of adjacent equal entries; a level sequence
  w_1 ⋯ w_n has w_1 = 0 and w_i ≤ 1 + lev(w_1 ⋯ w_{i−1}) for 2 ≤ i ≤ n; containment of a pattern means a
  subsequence order-isomorphic to it, with equal entries preserved.
- Locator: Section 4, Class 12, Problem 1: F_{101,102}(x) = (1 − √(1 − 4x))/(2x) − 1, verified there through
  the coefficient of x^15.
- Locator: Section 6: "Problem 1 remains to be solved."

## Reading of the statement

The generating function counts nonempty sequences, so the statement says that the number of level
sequences of length n ≥ 1 avoiding 101 and 102 is the Catalan number C_n: 1, 2, 5, 14, 42, 132, 429, 1430,
4862 for n = 1, …, 9. All level sequences of length n are counted by the Bell numbers.

## Bounded prior-resolution evidence

Read on 2026-10-02: the publisher page refused direct access; the statement and the section numbers above
were taken from the publisher full text as rendered through ResearchGate. The citation index records no
citing work, and searches of arXiv, OEIS and GitHub located no later treatment of the problem. This is a
bounded negative finding.
