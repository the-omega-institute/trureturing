---
bibkey: gleason1957measures
authors: Andrew M. Gleason
year: 1957
title: Measures on the Closed Subspaces of a Hilbert Space
doi: 10.1512/iumj.1957.6.56050
claim: Measures on Hilbert-space projections and their positive trace-operator representation in dimension at least three.
strata_touched:
  - D5/S3/Quantum/FiniteDimensional
license: citation-only
triage: anchor
---

# Measures on the Closed Subspaces of a Hilbert Space

Andrew M. Gleason characterizes normalized additive measures on the closed
subspaces of a Hilbert space by positive trace operators under the theorem's
dimension hypotheses. This is the literature anchor for the repository's
weaker forward skeleton: a positive semidefinite trace-one finite matrix gives
a normalized additive and nonnegative trace weight on projections.

The Lean theorem proves only that forward construction, for a finite decidable
index type. It does not prove Gleason representation or uniqueness, does not
impose or derive the dimension-at-least-three premise, and makes no
observer-ledger or forced-origin claim.

## Search log

- 2026-07-17: Queried NyxID/Tavily for `"Measures on the Closed Subspaces of
  a Hilbert Space" Gleason DOI`. Journal and DOI metadata verified Andrew M.
  Gleason, the 1957 title, and DOI `10.1512/iumj.1957.6.56050`.
- 2026-07-17: Queried `Gleason theorem density operator trace projection
  measure dimension at least three`. Results stated the normalized additive
  measure setting, positive trace-operator representation, and dimension
  restriction used to delimit the formal claim.
- 2026-07-17: Queried `positive density matrix trace rho P projection
  nonnegative proof`. Results matched the standard trace-probability
  construction; the noncommuting case was separately verified in Lean through
  the positive compression `P rho P*` and cyclicity of trace.

## Verified locator

- DOI: https://doi.org/10.1512/iumj.1957.6.56050
