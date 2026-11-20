---
bibkey: barrese2013mlevel
authors: Kenneth Barrese, Nicholas Loehr, Jeffrey Remmel, Bruce E. Sagan
year: 2013
title: "m-level rook placements"
doi: null
url: https://arxiv.org/abs/1308.4081v1
claim: "Proposition 4.4 gives the adjacent-root and conditional m-floor criterion for singleton Ferrers boards."
strata_touched:
  - D5/S3/Combinatorics/Partitions/RookRootCriterion
  - D5/S3/Combinatorics/Partitions/RookRootIndex
license: citation-only
triage: anchor
---

# Singleton root-vector admissibility

## Verified locator

URL: https://arxiv.org/abs/1308.4081v1. The primary full text is https://arxiv.org/html/1308.4081v1, Proposition 4.4 in Section 4. The proof of Theorem 4.5 uses the common padding length equal to the board area plus one.

## Source scope

Proposition 4.4 starts with a root vector whose first entry is zero and reconstructs column heights by subtracting each root from its position times m. Its first adjacent condition is equivalent to nonnegative weakly increasing column heights. Its second condition compares the m-floors of adjacent roots only when neither root is a multiple of m, and is equivalent to the geometric singleton condition.

RookRootCriterion supplies the nonnegative weakly increasing column tuple explicitly and proves the conditional floor clause equivalent to having at most one partial column ending in each level. Integer Euclidean division by positive m gives the same comparison as the source m-floor. The root index separately retains the first-zero and Ferrers conditions. Equal root values have no separate labels.

This source does not provide the registered evaluated count of an entire m-level rook equivalence class. Its known root-vector criterion and padding route are prerequisites; no resolution of the whole-class question or claim of literature novelty follows from their formalization.
