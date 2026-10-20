---
bibkey: mathlib2026powerseriesfrobenius
authors: The mathlib Community
year: 2026
title: "Mathlib formal power series: Frobenius and expansion"
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/PowerSeries/Expand.lean
claim: "Over ZMod p for prime p, the p-th power of a formal series equals its substitution at X^p."
strata_touched:
  - D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity
license: citation-only
triage: anchor
---

## Verified locator

Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/PowerSeries/Expand.lean

# Frobenius and monomial substitution

The pinned Mathlib result `MvPowerSeries.map_frobenius_expand` identifies expansion
with Frobenius after mapping the coefficient ring. Over `ZMod p`,
`ZMod.frobenius_zmod` makes the coefficient map the identity.
`PowerSeries.expand_apply` identifies expansion by `p` with substitution at
`X^p`. These statements give the displayed formula of
`CubicFifteenSubstitutionParity.prime_power_subst`.

This is an application of Mathlib's Frobenius and expansion identities.
