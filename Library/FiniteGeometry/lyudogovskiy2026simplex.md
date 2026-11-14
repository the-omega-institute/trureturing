---
bibkey: lyudogovskiy2026simplex
authors: Fedor B. Lyudogovskiy
year: 2026
title: "Simplex Stratification and Phase Boundaries in the Partition Graph"
doi: null
url: https://arxiv.org/html/2603.23228v1
claim: "Conjectures 5.1 and 5.2, repeated as Problems 6.1 and 6.2, ask for the complete triangular threshold and staircase first-occurrence family of exact local simplex layers."
strata_touched:
  - D5/S3/Combinatorics/Partitions/LyudogovskiyTransfers
  - D5/S3/Combinatorics/Partitions/LyudogovskiySimplex
license: citation-only
triage: anchor
---

# Local simplex layers in the integer-partition graph

The graph has every integer partition of a positive integer n as a vertex.
An edge transfers one unit between distinct part occurrences, permits a new
part, erases a zero remainder, and reorders. Equal resulting partitions are
excluded. The local dimension at a vertex is the greatest cardinality of a
clique containing it, minus one. L_r(n) is the exact dimension-r level.
The threshold tau(r) is the least positive n for which that level is nonempty.

Conjecture 5.1 and Problem 6.1 ask whether tau(r)=1+r(r+1)/2 for every
nonnegative r, and whether the maximum local dimension at every positive n
is max{r:1+r(r+1)/2<=n}. Conjecture 5.2 and Problem 6.2 ask whether, for
every r>=2, the entire first level L_r(tau(r)) consists precisely of the
one-cell addable extensions of the staircase (r,r-1,...,1).

The star/top clique mechanism is classical support: see this paper's
Proposition 3.3 and arXiv:2603.14370v1, Theorem 3.6. The minimal staircase
for a prescribed number of distinct positive sizes is also support, appearing
in arXiv:2604.11837v1, Theorem 2.5 and Corollary 2.6. Neither support fact
alone answers either full local-layer question. arXiv:2603.29988v1,
Problems 8.1 and 8.2, restates the same questions.

The bounded source comparison found no complete answer in the inspected
target-relevant portions of the author's sixteen indexed papers. This does
not establish worldwide priority or exhaustive absence of an equivalent
result. The formal endpoints `LyudogovskiySimplex.threshold_result` and
`LyudogovskiySimplex.first_occurrence_result` cover the two full questions.
The classical support facts and later aliases are not additional settlements.

## Verified locator

https://arxiv.org/html/2603.23228v1
