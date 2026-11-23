---
bibkey: trureturing2026fibonaccimixedqubit
authors: trureturing research synthesis
year: 2026
title: Supported joint convexity and the Fibonacci mixed-qubit margin
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: The pure Fibonacci trace-log deficit extends to arbitrary trace-one PSD qubit triples by supported joint convexity and independent spectral averaging.
strata_touched:
  - D5/S3/Quantum/Divergence/SupportedTraceLog
  - D5/S3/Quantum/Divergence/Qubit/FibonacciMixedQubit
license: Apache-2.0
triage: anchor
---

# Supported joint convexity and the Fibonacci mixed-qubit margin

## Verified locator

The normalized finite matrix log-sum inequality is
`FannesRootFidelityHolevo.matrix_log_sum` at its original private declaration.
It uses `CanonicalChannelDPI.extended_quantum_relative_entropy_channel_dpi`
with the channel that erases a finite block label. The logarithm scaling
identity is `Matrix.IsHermitian.log_smul_of_ne_zero` in the vendored
Physlib `HermitianMat/LogExp.lean`.
[trureturing](https://github.com/the-omega-institute/trureturing) · [Normalized log-sum and flag erasure](https://github.com/the-omega-institute/trureturing/blob/1be4a25323ffaad591f683bd3cb9dd77fb33342c/D5/S3/Quantum/Divergence/FannesRootFidelityHolevo.lean#L617)

The pure margin is `FibonacciClippedProfile.traceLog_le_benchmark_sub_margin`.
Its forward-profile input uses Hirche and Tomamichel, Corollary 2.3.
The mixed proof uses `PetzSpectralCoordinates.cfc_spectral_sum` at the
identity function and `SignedProfile.trace_pair` for the rank-one product trace.
[Pure margin](https://github.com/the-omega-institute/trureturing/blob/1be4a25323ffaad591f683bd3cb9dd77fb33342c/D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.lean#L912) · [Hirche and Tomamichel](https://arxiv.org/abs/2306.12343)

## Formalization scope

For common nonnegative weights and finite supported PSD pairs, there is
no trace normalization requirement. The proof uses the spectral support
projection to absorb logarithmic scaling terms on the numerator, normalizes
nonzero aggregate traces, cancels their scale correction by trace additivity,
and handles zero blocks by the PSD order and homogeneity at weight zero.

For three trace-one PSD matrices of size two, use numerator weights
\((88,25,28)/141\) and reference weights \((66,15,12)/141\).
The reference has trace \(31/47\). Each of the eight pure triples carries the
product of all three selected eigenvalues. One-coordinate marginals
reconstruct both mixtures. Two-coordinate marginals give
\(\operatorname{Re}\operatorname{Tr}(X_1X_2)\) and
\(\operatorname{Re}\operatorname{Tr}(X_1X_3)\).
The benchmark is \((113/141)\log(113/81)+(28/141)\log(7/3)\), and the
deficit is
\((3(1-\operatorname{Re}\operatorname{Tr}(X_1X_2))+11\operatorname{Re}\operatorname{Tr}(X_1X_3))/63360\).
The inequality includes singular references and pure preparations. The result
concerns the three positive-likelihood preparations on a qubit.
