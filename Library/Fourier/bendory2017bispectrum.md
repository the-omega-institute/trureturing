---
bibkey: bendory2017bispectrum
authors: Tamir Bendory, Nicolas Boumal, Chao Ma, Zhizhen Zhao, Amit Singer
year: 2017
title: Bispectrum Inversion with Application to Multireference Alignment
doi: 10.1109/TSP.2017.2775591
url: https://arxiv.org/abs/1705.00641v2
claim: Proposition II.2 gives source-dependent local stable bispectrum inversion for real or complex signals with nonvanishing DFT, using Frobenius error on a bispectrum estimator.
strata_touched:
  - D5/S3/Fourier/DCDominantFullBispectrumStability
license: citation-only
triage: anchor
---

# Stable inversion and conventions

Proposition II.2 states that an estimator exists such that, for each real or
complex signal x with nonvanishing DFT, there are constants delta(x)>0 and
L(x)<infinity. If an estimated bispectrum differs from the true bispectrum
by at most delta(x) in Frobenius norm, the estimator's signal error, minimized
over circular shifts in counting Euclidean norm, is at most L(x) times that
Frobenius error. These constants depend on the source signal. This is an
uncalibrated local inverse result, so removal of independent DC calibration
is not claimed as new here.

Equation II.3 uses the unnormalized negative-exponent DFT: translating x to
x(n-s) multiplies its kth coefficient by exp(-2 pi i k s/N). Equation II.5
writes the bispectrum as y(k1) conjugate(y(k2)) y(k2-k1). The bijective index
change (k1,k2)=(k,k+l) gives y(k)y(l)conjugate(y(k+l)), the convention used
by DCDominantFullBispectrumStability. This permutation preserves the set of
entries, the uniform entrywise error, and the Frobenius norm. Uniform
entrywise error epsilon on N squared entries implies Frobenius error at
most N epsilon; the two error hypotheses are not interchangeable with a
dimension-independent constant.

The repository theorem compares the true full bispectra of two actual
complex signals, assumes a positive source spectral lower bound and source
DC dominance, and gives the explicit radius 2 epsilon/m squared, including
signal-ball uniqueness. It does not construct the paper's estimator on
arbitrary perturbed matrices. The explicit estimate is a repository
synthesis using existing phase correction; no literature novelty claim
is attached to it.

## Verified locator

- DOI: https://doi.org/10.1109/TSP.2017.2775591
- Versioned source: https://arxiv.org/abs/1705.00641v2
- Full text: https://ar5iv.labs.arxiv.org/html/1705.00641; Section II,
  equations II.3 and II.5, and Proposition II.2. The arXiv record lists
  the original posting as 2017-05-01 and version 2 as 2017-10-06.
