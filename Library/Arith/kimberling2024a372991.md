---
bibkey: kimberling2024a372991
authors: Clark Kimberling; R. J. Mathar
year: 2024
title: OEIS A372991, a(n) = (2n)!/(a(n-1)*a(n-2))
doi: null
url: https://oeis.org/A372991
claim: "Conjecture D-finite with recurrence a(n) -2*n*(2*n-1)*a(n-3)=0. - R. J. Mathar, Jul 16 2024"
strata_touched:
  - D5/S1/Recurrence/Invariants/FactorialQuotientRecurrence
license: citation-only
triage: anchor
---

# OEIS A372991

Clark Kimberling's entry, dated July 15, 2024, defines
`a(n) = (2n)!/(a(n-1)*a(n-2)), where a(0)=1, a(1) = 1.`
Mathar's formula of July 16, 2024 conjectures the displayed linear recurrence,
with intended range `n >= 3`. The Lean module defines the quotient over the
rationals, proves positivity, cancels consecutive triple products, and proves
both the recurrence and natural-number integrality for all indices.

The orchestrator's oracle-read snapshot, fetched September 8, 2026, retains
the conjecture without a proof note and reports no proof by identifier search.
This implementation uses that supplied snapshot; it performed no network
lookup. Later OEIS edits and any literature beyond the supplied search are
ASSUMED-UNVERIFIED.

## Verified locator

- URL: https://oeis.org/A372991
