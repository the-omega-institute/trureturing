---
slug: cigler-boundary-motzkin-hankel
bibkey: cigler2022motzkin
doi: 10.48550/arXiv.2204.09910
url: https://arxiv.org/abs/2204.09910v4
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankel.result
---

# Reduced Denominators for Hankel Determinants of Boundary-Weighted Motzkin Paths

## Problem

Johann Cigler, *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin
paths*, arXiv:2204.09910v4, Section 2, Conjecture 2.1, equation (2.3). M_{n,k}(t,s) is the weighted number of Motzkin
paths from (0,0) to (n,k) that never go below the axis, with up and down steps of weight 1, horizontal steps of weight s
at height 0 and t above; d_m(n,t,s) = det(M_{m+i+j,0}(t,s))_{0≤i,j<n}. With L_0 = 2, L_1 = t, L_r = tL_{r−1} − L_{r−2},
A_{0,0}(x,t) = 1 − x and A_{0,r}(x,t) = 1 − L_r(t)x + x² for r > 0, the conjecture states

Σ_{n≥0} d_m(n,t,s) xⁿ = R_m(x,t,s) / ∏_{j=0}^{⌊m/2⌋} A_{0,m−2j}(x,t)^{1+j(m−j)},

with R_m an integer polynomial in x, s, t of x-degree binom(m+1,3) + 1.

## Motivation

The theorem `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankel.result` establishes the identity for every m ≥ 1
over ℤ[t,s], with the exact x-degree of R_m.

## Gap

Pre-registration issue 12602 records the literature screen: the source records only the weaker denominator for s = t
(from Krattenthaler's Corollary 9); Chern–Shi, arXiv:2608.27208, settles other Hankel determinant conjectures of Cigler
for special boundary weights, and Cigler's arXiv:2309.15557 does not treat this statement. This is a bounded negative
finding.

## Route

1. An orthogonal-polynomial (Christoffel-type) formula writes d_m(n,t,s) as an m × m determinant of coefficients of the
   polynomials p_r(y) = F_r(y − t) + (t − s)F_{r−1}(y − t), confluent at the zero node.
2. Over a ring containing α with α + α^{−1} = t, the two Binet branches of p_r give d_m(n) = Σ_j α^{(m−2j)n} P_j(n);
   cancellation of same-branch Vandermonde factors bounds deg_n P_j by j(m − j).
3. A sequence of this shape has a rational generating function whose denominator is exactly the stated product;
   the identity descends to ℤ[t,s] without division by a discriminant that can vanish.
4. Extending the determinant to negative sizes, d_m(−a) = 0 for 1 ≤ a < m and d_m(−m) ≠ 0; this fixes the exact
   x-degree binom(m+1,3) + 1 of the numerator.

## Falsifier

The statement would fail if some branch contributed a polynomial factor of degree above j(m − j), or if the first
nonzero negative-index determinant vanished identically in s and t.

## Evidence

An independent referee implementation checked the identity symbolically in s and t for m ≤ 5 and for many integer
pairs (s, t), including t = ±2 and s = t, for m ≤ 7.

## Triage

`theorem`; the statement is Conjecture 2.1 of arXiv:2204.09910v4 and is quantified over every m ≥ 1.

- Proved (formalized): the reduced denominator ∏_j A_{0,m−2j}^{1+j(m−j)} and the exact numerator degree
  binom(m+1,3) + 1, for every m ≥ 1, over ℤ[t,s].
- Proved (paper, refereed; formalization in progress, issue 12625): the same method gives Conjecture 1.3 of the paper
  for every column k, and hence Conjecture 1.2.
- Computed: Conjecture 2.2 of the paper fails as printed at k = m = 1: for t = s = 1 the sequences d_1^{(1)}(n,1,0)
  = 1, 1, 2, 3, 3, 4, 5, … and d_1^{(1)}(n,2,1) = 1, 1, 0, −1, −1, 0, 1, … admit no common nonzero linear recurrence
  of order 4 valid from n = 4 (the coefficient system on n ≤ 15 has rank 5).
- Open: whether the reduced exponents 1 + j(m − j) are attained, i.e. whether the stated denominator is the reduced
  one for every m.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv records named above, web and GitHub searches and the repository checks.
