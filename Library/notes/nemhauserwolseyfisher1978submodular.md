---
bibkey: nemhauserwolseyfisher1978submodular
authors: G. L. Nemhauser; L. A. Wolsey; M. L. Fisher
year: 1978
title: 'An Analysis of Approximations for Maximizing Submodular Set Functions—I'
doi: 10.1007/BF01588971
claim: Cardinality-greedy maximization of a normalized monotone submodular set function attains a one-minus-one-over-e approximation.
strata_touched:
  - D5/S3/Resource/SubmodularGreedyApproximation
license: citation-only
triage: anchor
---

# An Analysis of Approximations for Maximizing Submodular Set Functions—I

Nemhauser, Wolsey, and Fisher give the classical approximation analysis for
greedy maximization of a monotone submodular set function subject to a
cardinality constraint. The local formalization isolates the standard
diminishing-returns step, iterates the resulting geometric gap bound, and uses
the exponential estimate to obtain the one-minus-one-over-e factor.

## Search log

- 2026-09-01: Read the repository source bibliography for the selected atom.
  It identifies the authors, exact title, journal details, and DOI
  `10.1007/BF01588971`.
- 2026-09-01: Searched the existing D5 declarations for generic submodular
  greedy approximation bounds. Only concrete submodular functions and a
  one-step greedy optimizer were present; no cardinality-greedy constant bound
  matched.
- 2026-09-01: Searched pinned Mathlib for a generic submodular optimization
  package. No such theorem was present. The reusable terminal estimate was
  `Real.one_sub_div_pow_le_exp_neg`.

## Verified locator

- DOI: https://doi.org/10.1007/BF01588971
