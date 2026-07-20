---
bibkey: jaiswar2021identity
authors: Pintoo R. Jaiswar
year: 2021
title: Identity Theorem in Complex Analysis
doi: 10.37398/JSR.2021.650210
claim: Analytic functions agreeing locally on a connected complex domain agree throughout the domain.
strata_touched:
  - D5/S3/Zeros/CompletedZeta
license: citation-only
triage: anchor
---

# Identity Theorem in Complex Analysis

Pintoo R. Jaiswar states the one-variable complex identity theorem on an open
connected domain and derives the usual uniqueness consequence for analytic
functions. This is the literature anchor for the continuation-uniqueness
declaration in `D5/S3/Zeros/CompletedZeta`.

The Lean theorem uses mathlib's more set-oriented interface: both functions
are analytic on neighborhoods of a supplied preconnected set, a base point is
in that set, and equality holds eventually in the ambient neighborhood of the
base point. It does not formalize the CAS atom's explicit first-nonzero
coefficient estimate, geometric tail bound, path construction, or finite disc
cover. It also proves uniqueness only; it constructs no analytic continuation.

## Search log

- 2026-07-18: Queried NyxID/Tavily for `complex analysis identity theorem
  analytic functions connected domain book DOI`. The results stated the
  standard connected-domain theorem and returned the article together with
  DOI `10.37398/JSR.2021.650210`.
- 2026-07-18: Queried standard monographs by Ablowitz-Fokas, Conway, and
  Krantz-Parks. The searches confirmed textbook treatments of analytic
  continuation and identity principles, but the returned DOI-bearing Conway
  volume was not the volume clearly tied to the displayed theorem, while the
  Krantz-Parks result concerned real analytic functions. The direct complex
  identity-theorem article was therefore retained as the precise locator.

## Verified locator

- DOI: https://doi.org/10.37398/JSR.2021.650210
