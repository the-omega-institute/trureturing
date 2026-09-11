---
bibkey: quair2026projectiveangle
authors: QuAIR Team
year: 2026
title: Angular geometry of purified distance
doi: null
url: https://github.com/QuAIR/Lean-QIT/blob/c1d59b133b56e3d79efb11ee46a728d290f761f5/QIT/States/Geometry/PurifiedDistanceAngle.lean
claim: The projective angle arccos of the modulus of a pure-vector overlap satisfies the triangle inequality.
strata_touched:
  - D5/S3/QuantumBounds/FubiniStudyRecordTime
license: Apache-2.0
triage: anchor
---

# Projective angle triangle inequality

## Verified locator

The immutable source was retrieved and its complete `projectiveAngle_triangle` proof read:
https://github.com/QuAIR/Lean-QIT/blob/c1d59b133b56e3d79efb11ee46a728d290f761f5/QIT/States/Geometry/PurifiedDistanceAngle.lean

`QIT.PureVector.projectiveAngle_triangle` treats finite-dimensional normalized pure vectors.
It rotates the endpoint phases so that the two overlaps with the middle vector are real
and nonnegative, and applies Mathlib's real inner-product angle triangle inequality.
The present module adapts this proof to arbitrary complex inner product spaces and uses
`Complex.exists_norm_eq_mul_self` for the phases. No novelty is claimed for the geometry.

The upstream package pins Lean 4.30.0 and mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`; this repository pins Lean 4.33.0 and mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`, so the package cannot be added as a compatible
Lake dependency. The source copyright remains in the adapted module, and the full license
is retained in `docs/reports/recordtimebound/Lean-QIT-LICENSE.txt`.
The upstream tree contains no NOTICE file. Its original build and transitive axiom closure
were not rerun here; the adapted proof is checked under this repository's pinned kernel.

The conditional time and count consequences are repository derivations from the stated
physical displacement assumptions. This note attributes only the angular geometry to QuAIR.
