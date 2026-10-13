---
bibkey: roos2026positivepower
authors: Joris Roos; source proof authored by Codex
year: 2026
title: "LeanSpherical PlanarResolution: iterated derivatives of positive real powers"
doi: null
url: https://raw.githubusercontent.com/roos-j/lean-spherical/2b0e2bbf35cdf45ab99d1d77b2dea37b214fe236/LeanSpherical/Auto/Spherical/BRSRadial/PlanarResolution.lean
claim: "The pinned Lean source contains the classical falling-factorial formula for iterated derivatives of a real power on the positive half-line."
strata_touched: []
license: Apache-2.0
triage: anchor
---

# Positive-half-line derivative source

The pinned source is `roos-j/lean-spherical`, revision
`2b0e2bbf35cdf45ab99d1d77b2dea37b214fe236`, file
`LeanSpherical/Auto/Spherical/BRSRadial/PlanarResolution.lean`.
The source declaration is `iteratedDeriv_rpow_eqOn`. Its header identifies Joris Roos's copyright, Codex authorship and the
Apache 2.0 license. The source supplies the real-power derivative formula
used by `NonintegerForwardDifferenceSignal.iterated_deriv_rpow_pos`.

The mathematical identity is classical: on x>0, the n-th derivative of
x^p equals the product of p-i for 0<=i<n, times x^(p-n).
Attribution here identifies the Lean proof source rather than claiming
the formula originated in that source. The ported D5 source retains the
copyright and full Apache license text. This citation introduces no claim
that the upstream file is an admitted dependency of the repository.

## Verified locator

URL: https://raw.githubusercontent.com/roos-j/lean-spherical/2b0e2bbf35cdf45ab99d1d77b2dea37b214fe236/LeanSpherical/Auto/Spherical/BRSRadial/PlanarResolution.lean.
The URL returns the pinned Lean source and its attribution and license header.
