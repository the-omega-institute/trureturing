---
bibkey: kitware2026kyfanapproximation
authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh, and Claude Opus 5
year: 2026
title: Approximation-number min-max and finite Ky Fan triangle inequalities
doi: null
url: https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber
claim: Every finite prefix of rank-error approximation numbers satisfies the triangle inequality for bounded operators between complete complex Hilbert spaces.
strata_touched:
  - D5/S3/HilbertOperators/Approximation/KyFanTriangle
license: Apache-2.0
triage: anchor
---

# Native approximation-number Ky Fan triangle

The selected source is AIQ-Kitware/aiq-dkps-formalization revision
8924c4cc743d2f193bb4f39bee800790698a681b, under Apache-2.0.
The complex endpoint is ContinuousLinearMap.kyFanGauge_add_le_complex in
ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean, SHA-256
b25b4fdae0546ccc3795ee7301e76f371ef02a0c2b306f0294c75f4f6bc0c744.
The approximation number is the infimum of the actual operator-norm error over
bounded maps of rank at most n. The gauge is its finite prefix sum n < k.
The theorem retains independent source and target universes, completeness of
both complex Hilbert spaces, actual rectangular bounded maps, and every natural k.
It assumes neither compactness nor separability nor positive dimension.

The native proof reuses MinMaxLowerBound.exists_independent_lower_bound, the
existing finite rectangular variational upper bound and its original attaining
orthonormal pair, and the existing finite spectral decomposition and test-space
bounds in HermitianEigenvaluePerturbation. The additional argument constructs
spectral truncations, compares rank-bounded errors, transports finite coordinates,
compresses the joint range, and combines finite source restrictions.
No supplier SchurHorn or Singular.Subspace proof is imported or copied.
The finite rectangular proof retains its separate revision
64e234954217f3ca907ac980c8cbde2900109a66 and existing license notice.
The existing spectral support retains its LeanPool revision
bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8 and its notice chain.

These are classical approximation-number and Ky Fan results; no mathematical
novelty is claimed. They do not identify compact or Hilbert-Schmidt spectral
sequences, an infinite Ky Fan sum, Shirokov's cost J, or a convex roof.
Retire the adapted source slices when this repository's pinned Mathlib supplies
equivalent declarations with the same hypotheses, and use direct imports.

## Verified locator

https://github.com/AIQ-Kitware/aiq-dkps-formalization/tree/8924c4cc743d2f193bb4f39bee800790698a681b/ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber
