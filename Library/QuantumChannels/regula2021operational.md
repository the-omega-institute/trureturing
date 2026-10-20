---
bibkey: regula2021operational
authors: Bartosz Regula; Ryuji Takagi; Mile Gu
year: 2021
title: Operational applications of the diamond norm and related measures in quantifying the non-physicality of quantum maps
doi: 10.22331/q-2021-08-09-522
url: https://arxiv.org/abs/2102.07773v3
claim: Fourier diagonalization and constant-diagonal positive and negative spectral parts yield an exact diamond norm for the inverse circulant dephasing maps treated in equations (70)–(74).
strata_touched: []
license: citation-only
triage: anchor
---

# Circulant Schur-map complete-norm calculations

## Source and locator

Literature status: `literature-attested`.

Regula, Takagi and Gu, *Quantum* 5, 522 (2021), [DOI](https://doi.org/10.22331/q-2021-08-09-522). The [author-hosted primary PDF](https://bartoszregula.me/pdf/q-2021-08-09-522.pdf), matching arXiv:2102.07773v3, gives the relevant calculation on printed pages 18–19, equations (70)–(74). Fourier eigenvectors make the positive and negative spectral parts have constant diagonals, supplying completely positive majorants and a matching trace-norm expression for the inverse dephasing maps considered there.

## RT use and boundary

[RT IV §107](../../docs/develop/theory/ARITHMETIC_HOLOGRAPHIC_RT_IV.md#107-sharp-original-channel-bound-from-one-cyclic-correct-output-gram) uses this established spectral method as an intermediate tool. Its original channels map eight logical coordinates to four output fibres, so the scalar Schur normalization from the source is not substituted for the original complete norm. The RT proof supplies matching original fibre-block primal and dual certificates, then proves the parity-convolution inequality, the sharp constant, physical attainment and the leakage-safe extension.

The RT result assumes that one correct-output Gram is circulant in a stated original-coordinate labeling, possibly after reciprocal phases and an original-fibre-preserving relabeling. A fixed-party convex average reduces the other Gram to the simultaneous-cyclic calculation. It does not average arbitrary channel pairs into this class, exclude the whole residual rank class, or prove the unrestricted quarter optimum. No exhaustive literature-priority claim is made.
