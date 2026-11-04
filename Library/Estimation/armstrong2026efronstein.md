---
bibkey: armstrong2026efronstein
authors: Scott N. Armstrong
year: 2026
title: CoarseGraining Efron-Stein source proof
claim: The bounded finite-product Efron-Stein inequality is supplied by the three-file source closure at the immutable revision below.
doi: null
strata_touched:
  - D5/S3/Analytic/Probability/EfronStein
license: Apache-2.0
triage: anchor
url: https://github.com/scottnarmstrong/CoarseGraining/tree/310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be/Homogenization/Probability/EfronStein
---

## Source and license correspondence

The Lean source is `scottnarmstrong/CoarseGraining@310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be`, files `Homogenization/Probability/EfronStein/TwoPoint.lean`, `ProdDecomp.lean`, and `Fin.lean`. Their SHA-256 values are respectively `5a98004c7f081484a63326763d6d6259e771fdf94acc63756352d082516fee66`, `c03cf8e23cadaed17f7021d6c845edeb122221681f828c21b90f2617639ad3d1`, and `7375fe8b3e9fd00d63f4e7cf33f25362f6bde98d8558b89f91cb2c2d257bc95e`.

The complete immutable Apache-2.0 license is retained at `docs/reports/licenses/coarsegraining-efron-stein/LICENSE.txt`. The receiver adds a prominent modification notice in the Lean host and uses only direct Mathlib imports. The original source tree has no NOTICE file. The matching-pin LeanPool mirror is not a dependency or the supplier of this port; its separate NOTICE chain is not used.

The paper metadata for J. Michael Steele, “An Efron-Stein Inequality for Nonsymmetric Statistics,” is DOI `10.1214/aos/1176349952`. This note records source provenance; it does not claim that the paper text was downloaded or that the Lean source is an original result.

## Verified locator

- Immutable source revision: https://github.com/scottnarmstrong/CoarseGraining/tree/310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be/Homogenization/Probability/EfronStein
- DOI: https://doi.org/10.1214/aos/1176349952

## Receiving compatibility and retirement

The original source uses Lean 4.35.0-rc2 and Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55. The receiver uses Lean 4.35.0 and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. This pin mismatch selects the ordinary source-port form of SPEC A17.2. Consolidation keeps the finite-dimension induction and its consumed centering, Jensen, Fubini and reindexing support, with only the general finite-product endpoint public.

Retire the port and directly apply the upstream declaration when the receiver’s own pinned Mathlib contains an equivalent bounded finite-dependent-product Efron–Stein theorem with the same hypotheses, empty-index scope, coefficient and resampling integral order. Acceptance by an external upstream repository alone does not meet this retirement condition.
