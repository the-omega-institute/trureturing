---
bibkey: meiburg2026relative
authors: Alex Meiburg
year: 2026
title: Uniform power-slope control for singular relative-entropy limits
doi: null
url: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean
claim: The two-sided power difference quotient converges uniformly to x log x on every bounded nonnegative spectral interval, including zero.
strata_touched:
  - D5/S3/Quantum/Divergence/RenyiDivergence/UniformPowerSlope
license: Apache-2.0
triage: anchor
---

# Uniform power slopes at a singular endpoint

## Verified locator

The source is `QuantumInfo/Entropy/Relative.lean`, declaration
`rpow_slope_tendsto_uniformly`, at Physlib revision
`b9043cc548ef6d63a28454cf3a57fb12a0c2e142`:
https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean#L877

The source header credits Alex Meiburg, copyright 2026, and Apache 2.0.
The selected proof retains that header and attribution. The full supplier
license is `docs/reports/inoutbalance/physlib-LICENSE.txt`; the supplier root
has no NOTICE file. This selected proof does not include the supplier's
MIT-marked `HermitianMat/LiebConcavity.lean` material.

The estimate splits the spectral interval into a common neighborhood of
zero and a compact positive interval. Exponential domination controls both
signs of the exponent perturbation at zero; a uniform quadratic remainder
controls the compact interval. It imposes no positive lower spectral bound.
The zero term uses positive exponents near one and the convention
`0 * log 0 = 0`.

The canonical receiver retains only this supporting estimate. It does not
claim the variable-base matrix trace limit, operator Jensen, Lieb concavity,
data processing, quantum Pinsker, or the complete thermal recovery theorem.
There is no mathematical originality claim and no new external dependency.

Retire this port only when the receiver's own pinned Mathlib revision
contains a telescope-equivalent statement with arbitrary real upper bound,
both signs of the exponent perturbation, and the zero endpoint; its real
consumers must then use that declaration directly.
