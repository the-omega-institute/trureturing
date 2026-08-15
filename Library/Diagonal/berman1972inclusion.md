---
bibkey: berman1972inclusion
authors: Gerald Berman and K. D. Fryer
year: 1972
title: 'The Inclusion-Exclusion Principle'
doi: 10.1016/b978-0-12-092750-0.50008-9
claim: The indicator of a finite union is the alternating sum over nonempty subsets of the indicators of the corresponding intersections.
strata_touched:
  - D5/S0/Asymptotics/WeightedProbability/FiniteInclusionExclusion
license: citation-only
triage: anchor
---

# The Inclusion-Exclusion Principle

Berman and Fryer present the classical finite inclusion-exclusion identity.
For a finite family of events, the indicator of their union is the alternating
sum over nonempty subfamilies of the indicator of their intersection. Applying
this identity pointwise and summing against any finite weight function yields
the repository's exact weighted capture identity. No nonnegativity or
normalization is needed for that linear identity.

The repository-specific complement bridge additionally assumes normalized
marginals so that the frozen product sample weights sum to one. Nonnegativity
enters only when the first two cardinality truncations are compared with the
full sum through the frozen Bonferroni bounds.

## Search log

- 2026-08-15: Queried Crossref for `inclusion exclusion principle`. The result
  for DOI `10.1016/b978-0-12-092750-0.50008-9` identified Gerald Berman and
  K. D. Fryer, the exact chapter title, the 1972 publication year, and the
  containing book *Introduction to Combinatorics*.
- 2026-08-15: Searched pinned Mathlib for
  `inclusion.?exclusion|inclusion_exclusion|poincare`. The exact pointwise
  theorem `Finset.indicator_biUnion_eq_sum_powerset` was found in
  `Mathlib/Combinatorics/Enumerative/InclusionExclusion.lean` and is applied
  directly by the Lean proof.
- 2026-08-15: Searched `D5/` for `capture.*inclusion`,
  `escape.*powerset`, and `powerset.*Captured`. No exact weighted capture
  inclusion-exclusion declaration was present.

## Verified locator

- DOI: https://doi.org/10.1016/b978-0-12-092750-0.50008-9
