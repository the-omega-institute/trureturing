---
bibkey: ishida2026shield
authors: Yoshiteru Ishida
year: 2026
title: "A Quadratic Lower Bound for the Shield Number of the Stable Marriage Problem: Rearrangement, Extremal Construction, and Biclique Realizability"
doi: 10.48550/arXiv.2609.17418
url: https://arxiv.org/abs/2609.17418v1
claim: "The cyclic ranks (1) define C_n; the general upper bound β(C_n) ≤ ⌊(n − 1)²/4⌋ is left open in Section 7.1 and the conclusion."
strata_touched:
  - D5/S3/Combinatorics/Graph/CyclicStableMarriageBlockingBound
license: citation-only
triage: anchor
---

# Ishida's cyclic stable-marriage profile and arc-lemma question

The shield number minimizes, over strict complete preference profiles, the largest number of
blocking pairs of a complete matching. The cyclic Hollow-Shell profile is a distinguished profile
for the Shield-Core conjecture.

## Verified locator

DOI: 10.48550/arXiv.2609.17418

URL: https://arxiv.org/abs/2609.17418v1

Section 1.1, pp. 1–2: the blocking-pair and blocking-count definitions and cyclic profile (1).
Section 5, pp. 5–6: Proposition 5.1 and Theorem 5.3.
Section 7.1, p. 8: the open upper-bound problem.
Conclusion, p. 10: the general upper bound is outside the paper's proved results.

## Source statements

Equation (1), p. 2:

> r_M(g, h) = (h − g) mod n + 1, r_W(h, g) = n − (h − g) mod n

Section 1.1, p. 1:

> A complete matching µ (a bijection from men to women) has a blocking pair (m_i, w_j) if
> m_i prefers w_j to µ(m_i) and w_j prefers m_i to µ^{−1}(w_j)

> write B_S(µ) for their number in instance S and β(S) = max_µ B_S(µ)

Section 7.1, p. 8:

> This statement does not assert that µ∗ is maximum-blocking; that is exactly the open arc-lemma
> upper-bound problem.

Conclusion, p. 10:

> It does not claim the exact Shield-Core equality for general n, a universal Hall-feasible biclique
> theorem, or the general upper bound β(C_n) ≤ ⌊(n − 1)²/4⌋.

## Reading

The labels on each side are 0 through n − 1, and lower ranks are preferred. A complete matching
is a permutation of the labels. Each ordered man-woman pair is counted once. Integer Euclidean
remainder represents the source's modular difference, including negative label differences.
The upper bound on the maximum is equivalent to the same bound for every permutation, for each
n ≥ 1. Natural-number division by four represents the floor.

Theorem 5.3 supplies a matching attaining the proposed upper bound. Together with an upper-bound
proof, it gives the second equality of the Shield-Core conjecture. The first equality, which compares
the cyclic profile with all preference profiles, is a separate question.
