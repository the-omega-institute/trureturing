---
slug: andrews-el-bachraoui-d23-sign-pattern
bibkey: andrews2025positive
doi: 10.48550/arXiv.2507.09276
url: https://arxiv.org/abs/2507.09276v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFour.result
---

# The Negative Coefficients of the Two-Color Partition Series D'(2,3,n)

## Problem

George E. Andrews and Mohamed El Bachraoui, *Certain positive q-series and inequalities for two-color partitions*,
arXiv:2507.09276v1, Section 3, Conjecture 4. With
Σ_n D'(k,m,n) qⁿ = Σ_{j≥0} q^{m(2j+2)} (q^{2j+4}, q^{2j+2+2k}; q²)_∞ / (q^{2j+3}; q²)_∞² (equation (1.3)), the
conjecture states that the only negative coefficients of Σ_n D'(2,3,n) qⁿ occur at n = 10 and n = 22.

## Motivation

The theorem `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiFour.result` establishes that D'(2,3,n) < 0
holds exactly for n = 10 and n = 22.

## Gap

Pre-registration issue 12707 records the literature screen: Chern and Wang, arXiv:2601.19845, prove only the m = 1
family; the later papers of El Bachraoui and coauthors do not treat Conjecture 4. This is a bounded negative finding.

## Route

1. Theorem 4 and Theorem 1 of the paper for k = 2, m = 3, together with finite partial fractions, give an exact
   formula for D'(2,3,n) in terms of the triangular-pair count of Gauss's identity and divisor sums twisted by a
   character modulo small moduli.
2. A hyperbola decomposition with constant one bounds the character sums; together with the triangular-pair bound
   this gives D'(2,3,n) ≥ 0 for n ≥ 419.
3. The indices below 419 are checked by kernel computation; the only negative values are D'(2,3,10) = D'(2,3,22) = −1.

## Falsifier

The statement would fail at an index n ∉ {10, 22} with D'(2,3,n) < 0, or if D'(2,3,10) or D'(2,3,22) were
nonnegative.

## Evidence

An independent referee implementation checked the exact coefficient formula and the sign pattern from the definitions
for every n ≤ 5000.

## Triage

`theorem`; the statement is Conjecture 4 of arXiv:2507.09276v1, quantified over every n ≥ 0.

- Proved (formalized): D'(2,3,n) < 0 exactly for n = 10 and n = 22, where the value is −1.
- Open: Conjecture 5, eventual positivity of D'(k,m) for k > m.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv records named in issue 12707, web and GitHub searches and the
repository checks.
