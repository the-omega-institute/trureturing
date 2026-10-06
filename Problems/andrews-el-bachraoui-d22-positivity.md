---
slug: andrews-el-bachraoui-d22-positivity
bibkey: andrews2025positive
doi: 10.48550/arXiv.2507.09276
url: https://arxiv.org/abs/2507.09276v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiThree.result
---

# Positivity of the Two-Color Partition Series D'(2,2,n)

## Problem

George E. Andrews and Mohamed El Bachraoui, *Certain positive q-series and inequalities for two-color partitions*,
arXiv:2507.09276v1, Section 3, Conjecture 3. With
Σ_n D'(k,m,n) qⁿ = Σ_{j≥0} q^{m(2j+2)} (q^{2j+4}, q^{2j+2+2k}; q²)_∞ / (q^{2j+3}; q²)_∞² (equation (1.3)), the
conjecture states that D'(2,2,n) ≥ 0 for every n ≥ 0. Equivalently, among the two-color partitions of Definition 2
with k = m = 2, those with an odd number of even parts above the smallest part never outnumber those with an even
number.

## Motivation

The theorem `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiThree.result` establishes D'(2,2,n) ≥ 0 for
every n ≥ 0.

## Gap

Pre-registration issue 12707 records the literature screen: Chern and Wang, arXiv:2601.19845, prove the m = 1 family
(Conjecture 1) and do not treat Conjectures 2–4; the later papers 2512.23391, 2604.02239, 2604.08013, 2606.30208,
2607.10576 and 2609.05961 by El Bachraoui and coauthors do not treat them either. This is a bounded negative finding.

## Route

1. Theorem 4 of the paper and Theorem 1 for k = m = 2 (a finite Heine-type q-binomial identity) express the series
   through q²/(1 − q)² minus a Lambert series and the product (q², q⁴; q²)_∞ / (q; q²)_∞².
2. Gauss's triangular-number identity, derived from a formal Jacobi triple product proved by a Durfee-square
   decomposition, identifies the product's coefficients with S(n) = #{(a,b,c) ∈ ℕ³ : T_a + T_b + 2c = n}, and the
   Lambert coefficient is τ(2n + 5) − 2 by an odd-factor bijection. Hence D'(2,2,n) = n + 3 − S(n) − τ(2n + 5).
3. An injective encoding of parity-compatible triangular rows and a square-root bound for odd divisors give
   S(n) + τ(2n + 5) ≤ n + 3 for n ≥ 172; the indices below 172 are checked by kernel computation.

## Falsifier

The statement would fail at an index n with S(n) + τ(2n + 5) > n + 3.

## Evidence

An independent referee implementation checked the coefficient formula and the inequality from the definitions for
every n ≤ 5000. Equality D'(2,2,n) = 0 holds at n = 0, 1, 2, 3, 5, 6, 8, 11, 15, 20.

## Triage

`theorem`; the statement is Conjecture 3 of arXiv:2507.09276v1, quantified over every n ≥ 0.

- Proved (formalized): D'(2,2,n) = n + 3 − S(n) − τ(2n + 5) ≥ 0 for every n.
- Proved (paper): Conjecture 4, that D'(2,3,n) < 0 exactly for n = 10 and n = 22 (both values −1), and
  Conjecture 2, that C'(2,4,n) ≥ 0, by analogous exact coefficient formulas with character sums and thresholds 419
  and 1203; their formalization is in progress.
- Open: Conjecture 5, eventual positivity of D'(k,m) for k > m.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv records named above, web and GitHub searches and the repository
checks.
