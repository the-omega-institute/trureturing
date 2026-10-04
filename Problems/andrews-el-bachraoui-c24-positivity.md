---
slug: andrews-el-bachraoui-c24-positivity
bibkey: andrews2025positive
doi: 10.48550/arXiv.2507.09276
url: https://arxiv.org/abs/2507.09276v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiTwo.result
---

# Positivity of the Two-Color Partition Series C'(2,4,n)

## Problem

George E. Andrews and Mohamed El Bachraoui, *Certain positive q-series and inequalities for two-color partitions*,
arXiv:2507.09276v1, Section 2, Conjecture 2. With
Σ_n C'(k,m,n) qⁿ = Σ_{j≥0} q^{m(2j+1)} (q^{2j+2}, q^{2j+2k}; q²)_∞ / (q^{2j+1}; q²)_∞² (equation (1.2)), the
conjecture states that C'(2,4,n) ≥ 0 for every n ≥ 0. In contrast, the paper notes that C'(2,5,n) changes sign.

## Motivation

The theorem `D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiTwo.result` establishes C'(2,4,n) ≥ 0 for
every n ≥ 0.

## Gap

Pre-registration issue 12707 records the literature screen: Chern and Wang, arXiv:2601.19845, prove only the m = 1
family; the later papers of El Bachraoui and coauthors do not treat Conjecture 2. This is a bounded negative finding.

## Route

1. Theorem 1 of the paper for k = 2, m = 4 and finite partial fractions give an exact formula for C'(2,4,n) in terms
   of the triangular-pair count of Gauss's identity, a periodic term, and weighted divisor sums.
2. A weighted hyperbola decomposition with exact cancellation of its main term bounds the divisor sums; with the
   triangular-pair bound this gives C'(2,4,n) ≥ 0 for n ≥ 1203.
3. The indices below 1203 are checked by kernel computation.

## Falsifier

The statement would fail at an index n with C'(2,4,n) < 0.

## Evidence

An independent referee implementation checked the exact coefficient formula and the positivity from the definitions
for every n ≤ 5000. Direct expansion shows that C'(2,5,n) is first negative at n = 688.

## Triage

`theorem`; the statement is Conjecture 2 of arXiv:2507.09276v1, quantified over every n ≥ 0.

- Proved (formalized): C'(2,4,n) ≥ 0 for every n.
- Computed: C'(2,5,n) < 0 at n = 688, 690, 692, 887, …, so the analogue for m = 5 fails, as the paper states.
- Open: a description of the pairs (k,m) for which Σ_n C'(k,m,n) qⁿ is positive.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv records named in issue 12707, web and GitHub searches and the
repository checks.
