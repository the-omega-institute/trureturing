---
slug: caro-petrusevski-skrekovski-tuza-grid-three-eighths
bibkey: caro2025oddindependencegrids
doi: null
url: https://arxiv.org/abs/2510.01897v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/OddIndependence/OddGrid.result
---

# Dense Independent Sets of the Square Grid Contain a Full Cross

## Problem

Y. Caro, M. Petruševski, R. Škrekovski and Zs. Tuza, *The odd independence number of graphs, II:
Finite and infinite grids and chessboard graphs*, arXiv:2510.01897v1, Problem 29: does there exist a
sequence ε_n with ε_n → 0 such that any (3/8 + ε_n)n² independent vertices of P_n □ P_n contain all
four neighbours of some vertex?

## Motivation

The theorem `D5/S3/Combinatorics/OddIndependence/OddGrid.result` answers the question affirmatively
with ε_n = 4/n. By the paper's remark after Problem 29, this determines the odd independence density
of the infinite square grid: the paper's lower bound 3/8 is the exact value.

## Gap

The paper constructs independent sets of density 3/8 with no full cross and proves only the density
upper bound 5/13 for odd independent sets; the question for arbitrary independent sets without a
full cross was open. Pre-registration issue 13750 records the literature screen.

## Route

1. Extend S by zeros to the plane. For every 3 × 3 window M with no adjacent ones whose centre does
   not have all four neighbours in the set, 8w(M) + H(L) − H(R) + V(T) − V(B) ≤ 27, where w counts
   ones, L, R are the left and right 3 × 2 strips, T, B the top and bottom 2 × 3 strips, and H, V
   are fixed potentials with four nonzero values each (62 admissible windows, 12 with equality).
2. Summing over the (n + 2)² windows meeting the grid, the potentials telescope to all-zero boundary
   strips and each vertex is counted nine times, so 8|S| ≤ 3(n + 2)² whenever S has no full cross.
3. Since (3/8 + 4/n)n² > 3(n + 2)²/8 for n ≥ 1, a larger independent set contains a full cross.

## Falsifier

The theorem would fail if, for some n ≥ 1, an independent set of P_n □ P_n with more than 3(n +
2)²/8 vertices contained no vertex all four of whose neighbours lie in the set.

## Evidence

The local inequality was checked by exhaustive enumeration of the 512 binary 3 × 3 arrays before
formalization, and the maximum sizes for n ≤ 6 respect the bound; the formal proof is
kernel-checked.

## Triage

`theorem`; the statement is Problem 29 of arXiv:2510.01897v1.

- Proved (formalized): every independent set of P_n □ P_n without a full four-neighbour cross has at
  most 3(n + 2)²/8 vertices; Problem 29 holds with ε_n = 4/n.
- Not formalized: by the paper's remark after Problem 29, the affirmative answer settles the odd
  independence density of the infinite square grid at the paper's lower bound 3/8.
- Open: the higher-dimensional analogue, Conjecture 28 of the paper (density 1/3 in the limit of
  dimension d).

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv records of arXiv:2510.01897, arXiv:2509.20763 and
arXiv:2608.19024, arXiv searches for odd independence, a GitHub code search
(facebookresearch/atlas-lean defines odd independent sets only), and the repository checks. The
density consequence for the infinite grid relies on the paper's reduction and was not formalized.
