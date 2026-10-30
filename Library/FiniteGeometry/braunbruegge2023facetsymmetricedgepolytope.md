---
bibkey: braunbruegge2023facetsymmetricedgepolytope
authors: B. Braun, K. Bruegge
year: 2023
title: "Facets of Symmetric Edge Polytopes for Graphs with Few Edges"
doi: null
url: https://arxiv.org/abs/2201.13303v4
claim: "Conjecture 5.1: for the stated even and odd sums, F is maximized at the two endpoint triples and both coordinate transfers weakly increase F."
strata_touched:
  - D5/S3/Combinatorics/BinomialBases/BraunBrueggeFacetSumConjecture
license: citation-only
triage: anchor
---

# Braun–Bruegge symmetric edge-polytope facet sum

B. Braun and K. Bruegge, *Facets of Symmetric Edge Polytopes for Graphs with Few Edges*, arXiv:2201.13303v4 (6 July 2023). The source keeps Conjecture 5.1 in versions v1–v4; it is Conjecture 3.15 in v1.

Proposition 4.4 states: “If all the m_i's have the same parity, N(CB(m)) is given by F(m) = Σ_{j=0}^{m_t} C(m_t, j) [Π_{k=1}^{t−1} C(m_k, (m_k − m_t)/2 + j)].”

Conjecture 5.1 states: “For n = 2k and k ≥ 2 with x_1 + x_2 + x_3 = n + 1, F(x_1, x_2, x_3) is maximized at F(n − 1, 1, 1). For n = 2k − 1 and k ≥ 3 with x_1 + x_2 + x_3 = n + 1, F(x_1, x_2, x_3) is maximized at F(n − 3, 2, 2). Further, for any x_1 ≥ x_2 ≥ x_3 ≥ 3 all even or all odd positive integers, F(x_1, x_2, x_3) ≤ F(x_1 + 2, x_2, x_3 − 2) and F(x_1, x_2, x_3) ≤ F(x_1 + 2, x_2 − 2, x_3), when the subtraction by 2 will maintain the inequalities on the x_i's.”

The Lean encoding uses `Nat.choose`, natural floor division, and the admissible sorted domain recorded in the preregistration issue. The proof reduces the transfer to a centered binomial row, preserves the paired mass by Vandermonde, and applies a single-crossing weighted-sum inequality.

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2201.13303v4
