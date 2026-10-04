---
bibkey: tauceti2026gaussianpolynomial
authors: The Tau Ceti contributors; Rémy Degenne
year: 2026
title: Gaussian-polynomial totality through exponential-moment determinacy
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd
claim: Gaussian-polynomial tests at every positive width detect every complex Lebesgue L2 vector without a decay assumption on that vector.
strata_touched:
  - D5/S3/Quantum/Analysis/Hermite/GaussianPolynomialTotality
license: Apache-2.0
triage: anchor
---

# Gaussian-polynomial totality construction

Source: The Tau Ceti contributors, TauCetiProject/TauCeti,
revision `f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd` (Apache-2.0).

The retained source is adapted from:

- `TauCeti/Probability/Moments/Determinacy.lean`;
- `TauCeti/Probability/Moments/VanishingMoments.lean`;
- `TauCeti/Probability/Distributions/Gaussian/PolynomialMemLp.lean`.

The complex-MGF strip argument in Determinacy credits Mathlib's
`Mathlib/Probability/Moments/ComplexMGF.lean`, copyright 2025 Rémy Degenne.
That attribution is retained with the Tau Ceti copyright in the adapted source.
The full Apache-2.0 license is in
`docs/reports/hermite-suppliers/tauceti-LICENSE.txt`.
The exact donor source tree contains no file with NOTICE in its name.

The donor uses Lean `v4.35.0-rc3` and Mathlib
`b63f6e8a68d220e3b3bc4f3792bb53650d375f24`.
This repository uses Lean `v4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
The adapted port retains the original analytic and positive/negative density
construction as local proof steps in the actual Lebesgue Gaussian-polynomial
totality theorem. It introduces no separate moment-determinacy or normalization
statements, and makes no originality claim for the donor argument.

At a future Mathlib pin of this repository, retire the port when an exact direct
application proves the same totality statement for every positive Gaussian width
and the actual Hermite and physical-graph consumers still validate with the port
removed. Upstream acceptance at another pin is insufficient.

## Verified locator

https://github.com/TauCetiProject/TauCeti/tree/f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd

Attributed donor source scope at this revision:

- `TauCeti/Probability/Moments/Determinacy.lean`;
- `TauCeti/Probability/Moments/VanishingMoments.lean`;
- `TauCeti/Probability/Distributions/Gaussian/PolynomialMemLp.lean`.
