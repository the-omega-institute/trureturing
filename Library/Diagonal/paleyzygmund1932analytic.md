---
bibkey: paleyzygmund1932analytic
authors: R. E. A. C. Paley and A. Zygmund
year: 1932
title: A note on analytic functions in the unit circle
doi: 10.1017/s0305004100010112
claim: A nonnegative random variable has a lower-tail probability bounded below by a ratio of its first two moments.
strata_touched:
  - D5/S0/Diagonal/Probability/CaptureSecondMoment
license: citation-only
triage: anchor
---

# A Note on Analytic Functions in the Unit Circle

Paley and Zygmund introduced the second-moment inequality now bearing their
names. At threshold zero, a nonnegative random variable `N` satisfies
`P(N > 0) >= E[N]^2 / E[N^2]` whenever its second moment is positive.

The repository applies this finite form to the number of addresses satisfying
the already frozen `Captured` predicate. The proof is a direct finite weighted
Cauchy--Schwarz argument. The note anchors the inequality only; the capture
model, its product weights, and the identification of the mean with the sum of
one-address capture probabilities are repository-derived.

## Search log

- 2026-08-15: Searched pinned Mathlib for `Paley`, `Paley-Zygmund`, and
  `second moment`. No packaged inequality was found. The exact reusable hit was
  `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` in
  `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`.
- 2026-08-15: Searched `D5/S0/Diagonal` and `D5/S0/Asymptotics` for
  `variance`, `second moment`, `Paley`, and `Chebyshev`; all four searches were
  empty. `FiniteBonferroni` was read separately and proves different union
  bounds through private indicators.
- 2026-08-15: An initial candidate DOI,
  `10.1017/S0305004100010868`, returned HTTP 404 from Crossref and was rejected.
  A Crossref title-and-author query returned the exact article metadata and DOI
  recorded above; resolving that DOI returned volume 28, issue 3, pages 266-272.

## Verified locator

- DOI: https://doi.org/10.1017/s0305004100010112
