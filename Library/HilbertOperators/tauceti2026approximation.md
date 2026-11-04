---
bibkey: tauceti2026approximation
authors: The Tau Ceti contributors
year: 2026
title: Approximation numbers of bounded operators and infinite diagonal operators
doi: null
url: https://github.com/TauCetiProject/TauCeti/blob/b3de655482f7b86c77d8982566e5a73801fd64fa/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean
claim: Zero-based approximation numbers are infima over all bounded rank-at-most-n competitors; for infinite diagonal operators with decreasing coefficient magnitudes they equal those magnitudes.
strata_touched: []
license: Apache-2.0
triage: anchor
---

# Approximation numbers and diagonal operators

The cited immutable source defines approximation numbers using every bounded
competitor of actual cardinal rank at most the zero-based natural index.
Its scalar-generic definition uses nonnegative real operator norms.
The companion diagonal theorem compares finite truncations with arbitrary
competitors on the first n+1 coordinate vectors, and applies to real Hilbert
sequence spaces as well as other normed sequence spaces.

These are established approximation-number methods. The supported real
Hilbert-space comparison uses complete input and output coordinates and an
actual isometric inclusion of the output support. Its finite-dimensional
obstruction concerns the range of each competitor on the full input carrier.
The citations describe the background methods; they do not assert novelty of
the classical approximation theorem.

## Verified locator

The definition and the rank-bound infimum are at
https://github.com/TauCetiProject/TauCeti/blob/b3de655482f7b86c77d8982566e5a73801fd64fa/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean
in `ContinuousLinearMap.singularValue` and `isGLB_singularValue`.
The infinite diagonal comparison is `lp.singularValue_diagonalCLM` at
https://github.com/TauCetiProject/TauCeti/blob/b3de655482f7b86c77d8982566e5a73801fd64fa/TauCeti/Analysis/OperatorIdeal/ApproximationNumber/Diagonal.lean.
The latter cites A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University
Press, Chapter 2. Both Lean source headers identify the Tau Ceti contributors
and the Apache 2.0 license.
