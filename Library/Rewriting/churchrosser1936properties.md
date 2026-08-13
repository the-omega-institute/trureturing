---
bibkey: churchrosser1936properties
authors: Alonzo Church and J. B. Rosser
year: 1936
title: 'Some Properties of Conversion'
doi: 10.1090/S0002-9947-1936-1501858-0
claim: Convertibility coincides with joinability exactly when reduction is confluent.
strata_touched:
  - D5/S0/Rewriting/ChurchRosser
license: citation-only
triage: anchor
---

# Some Properties of Conversion

Church and Rosser's paper introduces the property now named after them: in a
reduction system where every divergence of reductions can be brought back
together, two terms are interconvertible precisely when they reduce to a common
term. The paper proves this for lambda-conversion; the abstract principle holds
for an arbitrary binary relation.

The repository declaration states the abstract equivalence: a relation is
confluent (any two reduction sequences from a common source are joinable) if and
only if convertibility — the equivalence closure of one-step reduction —
coincides with joinability through reflexive transitive closure. No termination
hypothesis appears; the equivalence is purely about the shape of reduction. A
corollary composes the equivalence with the frozen Newman confluence theorem.

## Search log

- 2026-08-13: Queried Crossref for DOI `10.1090/S0002-9947-1936-1501858-0`. The
  resolver returned Church and Rosser, the exact article title, 1936,
  *Transactions of the American Mathematical Society*, pages 472-482. The JSTOR
  alias `10.2307/1989762` did not resolve at Crossref and is not used.
- 2026-08-13: Searched the pinned Mathlib checkout for a confluence iff
  Church-Rosser equivalence. `Relation.church_rosser` gives a sufficient
  criterion only; the biconditional characterization is stated and proved
  directly in the repository declaration.

## Verified locator

- DOI: https://doi.org/10.1090/S0002-9947-1936-1501858-0
