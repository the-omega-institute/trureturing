---
bibkey: leeliu2025integerdomination
authors: Jia-Ying Lee; Chia-An Liu
year: 2025
title: The integer {2}-domination number of grids
doi: 10.48550/arXiv.2502.00134
url: https://arxiv.org/abs/2502.00134
claim: "Defines integer {2}-domination on Cartesian grids; Conjecture 2.5 asserts γ{2}(G3,n) = ⌊3n/2⌋ + 1 for every positive n, Remark 2.6 reports algorithmic evidence, Theorem 3.6 gives four-row values through n = 100, and Conjecture 3.7 asserts γ{2}(G4,n) = 2n − ⌊(n − 9)/10⌋ for n ≥ 49."
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2502.00134

Source: https://arxiv.org/abs/2502.00134

The quotations and page numbers refer to arXiv:2502.00134v1.

## Definitions

Section 1, p. 2: “For positive integers m and n, the grid graph Gm,n = Pm □ Pn is the
Cartesian product of path graphs Pm and Pn.”

Abstract, p. 1: “An integer {2}-dominating function of a graph is a mapping from the vertex
set to {0, 1, 2} such that the sum of the mapped values of each vertex and its neighbors
is at least 2; the integer {2}-domination number of a graph is defined to be the minimum
sum of mapped values of all vertices among all integer {2}-dominating functions.”

Section 1 permits nonnegative integer values; the abstract and Section 4 use {0, 1, 2}.
Capping a nonnegative integer value at 2 preserves the closed-neighbourhood inequalities
and does not increase the total weight, so the two minimum-weight formulations agree.

## Three-row conjecture

Conjecture 2.5, p. 11: “For positive integer n, we have γ{2}(G3,n) = ⌊3n/2⌋ + 1.”

Theorem 2.4, pp. 9–11, supplies the upper bound by an explicit alternating-column
construction. Remark 2.6, p. 11: “In fact, by an algorithm we propose in the next section,
the exact value of γ{2}(G3,n) is ⌊3n/2⌋ + 1 for any input positive integer n. However, it
is not sufficient for us to assert that γ{2}(G3,n) = ⌊3n/2⌋ + 1. As a future work, we
suggest that the methods proposed in [5] and [9] might be modified and applied on this problem.”

## Four-row results and further questions

Theorem 3.6, p. 17, gives the exact values for 1 ≤ n ≤ 100. Conjecture 3.7, p. 18:
“If n ≥ 49, then γ{2}(G4,n) = 2n − ⌊(n − 9)/10⌋.” The concluding remarks also ask for
other row counts and integer {k}-domination with k ≥ 3.
