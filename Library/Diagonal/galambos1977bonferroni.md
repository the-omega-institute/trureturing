---
bibkey: galambos1977bonferroni
authors: Janos Galambos
year: 1977
title: 'Bonferroni Inequalities'
doi: 10.1214/aop/1176995765
claim: First- and second-order Bonferroni inequalities give two-sided bounds for a finite union and hence for its complement.
strata_touched:
  - D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni
license: citation-only
triage: anchor
---

# Bonferroni Inequalities

Galambos gives the finite Bonferroni inequalities obtained by truncating the
inclusion-exclusion expansion. The repository uses the first two truncations
pointwise for finite capture events, multiplies them by nonnegative sample
weights, and sums. This yields the displayed lower and upper bounds on the
complement event, which is the escape probability.

The pinned Mathlib file
`Mathlib/Combinatorics/Enumerative/InclusionExclusion.lean` contains exact
inclusion-exclusion identities but not these truncated inequalities. The local
finite-indicator proof is therefore retained rather than duplicating an
available library theorem.

## Search log

- 2026-08-15: Queried Crossref for `Bonferroni inequalities`. The resolver
  returned Janos Galambos, the exact article title, 1977, *The Annals of
  Probability*, DOI `10.1214/aop/1176995765`.
- 2026-08-15: Searched the pinned Mathlib inclusion-exclusion module for
  Bonferroni and order-two truncated inequalities. Exact alternating-sum
  identities were present; the required inequalities were not.
- 2026-08-15: Searched `D5/` for a two-sided weighted escape bound. No
  pre-existing declaration matched.

## Verified locator

- DOI: https://doi.org/10.1214/aop/1176995765
