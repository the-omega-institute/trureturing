---
bibkey: vanlintwilson2001course
authors: J. H. van Lint and R. M. Wilson
year: 2001
title: A Course in Combinatorics
doi: 10.1017/cbo9780511987045
claim: Burnside's lemma identifies the number of orbits of a finite group action with the average number of points fixed by a group element.
strata_touched:
  - D5/S0/Diagonal/OrbitCounting/EquivariantListingOrbitCounting
license: citation-only
triage: anchor
---

# A Course in Combinatorics

Van Lint and Wilson present the classical orbit-counting lemma commonly called
Burnside's lemma: for a finite group acting on a finite set, the sum of the
fixed-point counts over the group equals the number of orbits times the group
cardinality.

The repository applies this result to the diagonal action on ordered pairs of
addresses. The separate identification of equivariant listings with functions
from the orbit quotient to the value type is repository-derived. Thus the
literature anchors the Burnside average, while the listing-space bridge and its
cardinality consequence remain formal consequences of the repository's
`IsEquivariant` definition.

## Search log

- 2026-08-15: Queried Crossref for DOI
  `10.1017/CBO9780511987045`. The response identified J. H. van Lint and
  R. M. Wilson, the title *A Course in Combinatorics*, the 2001 publication
  year, and Cambridge University Press.
- 2026-08-15: Searched pinned Mathlib for `Burnside`, `orbit counting`, and
  fixed-point/orbit cardinality patterns. The exact theorem
  `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` was found in
  `Mathlib/GroupTheory/GroupAction/Quotient.lean` and is applied directly.
- 2026-08-15: Searched `D5/` for equivariant-listing cardinalities,
  diagonal-action orbit quotients, and uses of the Mathlib Burnside theorem.
  The frozen tree contains a private transitive listing-cardinality lemma and
  the general escape-probability proof contains a local `hListingCard` for its
  denominator. Neither is an addressable declaration, and no public general
  orbit-counting bridge or Burnside expression was found.

## Verified locator

- DOI: https://doi.org/10.1017/cbo9780511987045
