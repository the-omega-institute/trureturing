---
bibkey: qiclean2026powerdecay
authors: TNLean contributors
year: 2026
title: Power decay below spectral radius one
doi: null
url: https://github.com/LionSR/QICLean/blob/c61daa23f385237a4d992a602c94812ca9f909b8/QICLean/Analysis/SpectralRadiusPowerDecay.lean
claim: In a complete complex normed algebra, every nonnegative rate strictly above an element's spectral radius bounds all its power norms by one positive constant times that rate to the power.
strata_touched:
  - D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary
license: Apache-2.0
triage: anchor
---

# Spectral-radius geometric bound

## Verified locator

https://github.com/LionSR/QICLean/blob/c61daa23f385237a4d992a602c94812ca9f909b8/QICLean/Analysis/SpectralRadiusPowerDecay.lean

The exact source is `geometric_bound_of_spectralRadius_lt` in
`QICLean/Analysis/SpectralRadiusPowerDecay.lean`, QICLean revision
`c61daa23f385237a4d992a602c94812ca9f909b8`. The source file's SHA-256 is
`a856a736209345bc21b31a2892af9d5b9d0a901b72b7e26bc0585c048425e3ef`.

For every type `A` with `NormedRing A`, `CompleteSpace A` and
`NormedAlgebra ℂ A`, every `a : A` and `rate : ℝ≥0` satisfying
`spectralRadius ℂ a < (rate : ℝ≥0∞)`, the theorem supplies
`∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖a ^ n‖ ≤ C * (rate : ℝ) ^ n`.
Its complete statement and proof are retained verbatim under the local name
`geometric_bound_supplier`. This consumed supplier is literature-attested;
the actual weighted-path and boundary conclusions retain their own provenance.

The source attribution is:

```text
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
```

The copyright attribution and full Apache-2.0 license are preserved in
[the receiving Lean source](../../D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/SpectralBoundary.lean).
The upstream `Notes/NOTICE.md` concerns only the lecture-note material in
`Notes/`; that material is not included in this supplier.
