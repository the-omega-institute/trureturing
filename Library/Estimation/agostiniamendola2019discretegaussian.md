---
bibkey: agostiniamendola2019discretegaussian
authors: Daniele Agostini and Carlos Améndola
year: 2019
title: Discrete Gaussian Distributions via Theta Functions
doi: 10.1137/18M1164937
url: https://arxiv.org/abs/1801.02373v2
claim: "Proposition 4.1 and Remark 4.2 express discrete Gaussian characteristic functions, cumulants, means and covariances through theta functions and their logarithmic derivatives."
strata_touched: []
license: citation-only
triage: anchor
---

# Discrete Gaussian normalizers and conditional cumulants

## Verified locator

DOI: <https://doi.org/10.1137/18M1164937>.
Crossref identifies the authors, title and *SIAM Journal on Applied
Algebra and Geometry* (2019), pp. 1–30. The directly inspected
[author version](https://arxiv.org/abs/1801.02373v2) has 23 PDF pages.
Its distribution definition, Proposition 4.1 and Remark 4.2 on
PDF pp. 10–12, including equations (4.20)–(4.23), were read.
The preprint's pagination is not the published pagination.

## Classical theta identities

For real $u$ and positive-definite real symmetric $B$, the mass
of the source's discrete Gaussian on $\mathbb Z^d$ is proportional to
$\exp(2\pi[-n^TBn/2+u^Tn])$, with normalizer $\theta(u,B)>0$.
Its cumulants satisfy

$$
\kappa_a=(2\pi)^{-|a|}\partial_u^a\log\theta(u,B).
$$

In particular,
$\mathbb EX_i=(2\pi)^{-1}\partial_{u_i}\log\theta$ and
$\operatorname{Cov}(X_i,X_j)=(2\pi)^{-2}
\partial_{u_i}\partial_{u_j}\log\theta$.
Equation (4.23) states the heat-equation relation to derivatives
in $B$, with different diagonal and off-diagonal coordinate factors.
The broader complex-parameter formulas exclude the theta divisor;
individual complex theta values are not assumed nonzero everywhere.

## Correspondence with the original periodic correction

Section 116 of the
[spectral-boundary volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
uses discrete Gaussian and wrapped-kernel normalizers, and derivatives
of a common conditional denominator. Those normalizer and cumulant
identities are classical. A probability interpretation uses the
positive real normalizer; it does not require every complex Fourier
mode to be nonzero.

This source does not estimate the distribution of the actual
fixed-size posterior centers, identify the original pair/path law
with a discrete Gaussian, or provide uniform error bounds as its
dimension and parameters change. The actual likelihood comparison,
calibration response, marked error estimates and modulo-one small
ball remain separate from these finite-dimensional identities.
