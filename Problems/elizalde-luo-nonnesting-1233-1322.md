---
slug: elizalde-luo-nonnesting-1233-1322
bibkey: elizalde2024pattern
doi: 10.48550/arXiv.2412.00336
url: https://arxiv.org/abs/2412.00336v6
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Nonnesting/NonnestingRoyalHigh.result
---

# Nonnesting Permutations Avoiding 1233 and 1322

## Problem

Sergi Elizalde and Amya Luo, *Pattern avoidance in nonnesting permutations*, arXiv:2412.00336v6,
Section 4, Table 4, row `{1233, 1322}`: the conjectured ordinary generating function is
`((1-x)^2 - √((1-x)^4 - 4x(1-x)^2))/(2x)` (OEIS A006319), with the remark

> All the conjectures have been checked for n up to 8.

## Motivation

The theorem `D5/S3/Combinatorics/Nonnesting/NonnestingRoyalHigh.result` establishes that the generating function R of
nonnesting permutations avoiding 1233 and 1322 satisfies `x R^2 - (1-x)^2 R + (1-x)^2 = 0`. This equation has a
unique power-series solution, the branch of the displayed square root with constant term one, so the counts
are `1, 1, 4, 16, 68, 304, 1412, 6752, …`.

## Gap

Pre-registration issue 11304 records the literature screen: none of the papers citing arXiv:2412.00336
treats this row, and the repository had no result for it. This is a bounded negative finding.

## Route

1. A nonnesting word is a permutation (its first-occurrence order) together with a Dyck word.
2. Pattern containment in such a word reduces to a local test on three letters.
3. A structural bijection maps the class onto the class avoiding {1132, 2213} (the two sets are not related by reversal, complement or reverse-complement), and the count of that class gives R = 1 + xR^2/(1-x)^2.

## Falsifier

The statement would fail if some n had a count different from the coefficient of the displayed series.
It depends on reading containment with equal letters kept equal.

## Evidence

Exhaustive enumeration through n = 8 agrees with every structural lemma and with the counts.

## Triage

`theorem`; the conjecture is stated in Table 4 of arXiv:2412.00336 and is quantified over every n.

## ASSUMED-UNVERIFIED

The literature screen is limited to the citation list, arXiv searches and repository checks recorded
above.
