---
bibkey: alpoge2026riemann
authors: Levent Alpöge
year: 2026
title: Riemann hypothesis formalization in Lean
doi: null
url: https://github.com/the-omega-institute/riemann-hypothesis
claim: Numerical Landau comparisons and the long power-window zero-exclusion route.
strata_touched:
  - D5/S3/Analytic/Laplace/LongWindowBounds
  - D5/S3/Analytic/Laplace/LongWindowPoleExclusion
  - D5/S3/CharacterSums/DirichletCyclicWindowZeroFree
license: citation-only
triage: anchor
---

# Riemann hypothesis formalization in Lean

## Verified locator

- URL: https://github.com/the-omega-institute/riemann-hypothesis
- Revision: `c7d25b3bfd7906388bb8eb0774e027a2b756a7b6`
- Directory: `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/`

## Source declarations

- `LandauGrowthContra.lean`, `Deduction.landau_growth_contra`: for positive c,d
  and d<e, there are positive eta and a cutoff U0 such that for all U>=U0 and
  natural k>=U, C exp(eta U)/e^k < c/d^k. Its proof chooses
  eta=log(e/d)/2 and U0=2|C|/(c log(e/d)).
- `landauWindow.lean`, `Deduction.landau_window_contra`: for positive c,d and
  d<e<=E, the two-error coefficient bound cannot recur at arbitrarily late U
  for every positive exponential loss eta.
- `landauWindow.lean`, `Deduction.landau_window`: the pole geometry, Cauchy
  coefficients and long-window moment estimates exclude poles on the right.
- `ZeroFreeOfRpowWindow.lean`, `Deduction.zeroFree_of_rpow_window`: the long
  power-window upper-bound hypothesis yields zero exclusion.

The numerical arguments above are literature-attested. The local declarations
retain that core and expose additional results: the growth theorem states the
chosen eta and nonnegative U0 explicitly; the window contradiction allows d<E
independently of d<e, using min(e,E). These strengthenings are repo-derived.

The local pole theorem allows theta>=0 and poles with real part at most one.
It exposes a fixed sigma>2, theta<sigma, E=sigma-theta, strict d<e<E,
nonnegative B,K, and the common order floor(sigma*((2+delta)/2)*U).
The actual cyclic-family application constructs its own arithmetic transform
and positive residues. Its final criterion allows every real theta. For
nonpositive theta the window premise is impossible, by the existing genuine
nontrivial zeta zero and a positive-exponent lift. This is not an extension of
the analytic continuation domain. These parts are repo-derived, not claims
that the pinned source states the strengthened local declarations verbatim.
