---
bibkey: pedro2026hermitelowering
authors: Leonardo Pedro
year: 2026
title: Probabilists Hermite polynomial lowering identity
doi: null
url: https://github.com/leonardopedro/timepiece/blob/61595bca99e3b8d8b8df51a2c3043b64597e24f9/BookProof/ChapterHermiteFunctions.lean
claim: Differentiating the degree n plus one probabilists Hermite polynomial gives n plus one times its predecessor.
strata_touched:
  - D5/S3/Quantum/Analysis/PhysicalHermiteTests
license: Apache-2.0
triage: anchor
---

# Hermite lowering identity

## Verified locator

https://github.com/leonardopedro/timepiece/blob/61595bca99e3b8d8b8df51a2c3043b64597e24f9/BookProof/ChapterHermiteFunctions.lean

Leonardo Pedro, Timepiece, revision
`61595bca99e3b8d8b8df51a2c3043b64597e24f9`,
`BookProof/ChapterHermiteFunctions.lean`, `derivative_hermiteR`.
The selected source has no file-level copyright header. Its named root grant
is `Copyright 2026 Leonardo Pedro`, preserved with the full Apache-2.0 terms in
`docs/reports/oscillator-suppliers/timepiece-LICENSE.txt`.
The authenticated donor tree has no NOTICE-named file.

The physical tensor proof uses the pinned Mathlib coefficient formula,
the derivative coefficient rule and the binomial identity
`Nat.add_one_mul_choose_eq` to obtain the lowering calculation locally.
The Gaussian and compact graph constructions carry the physical existence
and approximation result. The Timepiece differential calculations remain
attributed in that physical consumer.
