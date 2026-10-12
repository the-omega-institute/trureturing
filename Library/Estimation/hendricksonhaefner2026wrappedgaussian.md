---
bibkey: hendricksonhaefner2026wrappedgaussian
authors: Aaron J. Hendrickson and David P. Haefner
year: 2026
title: "Valley-peak modulation in phase space: a law-invariant VPM and its theta-function structure"
doi: null
url: https://arxiv.org/abs/2603.01199v3
claim: "Section 3 removes an arbitrary integer-valued additive signal by reduction modulo one; equations (7)–(8) give the resulting wrapped Gaussian and Jacobi theta representations."
strata_touched: []
license: citation-only
triage: anchor
---

# Wrapped Gaussian positivity and the original empirical phase

## Verified locator

The [arXiv version](https://arxiv.org/abs/2603.01199v3) and its
11-page PDF are accessible with HTTP 200. The title and authors
match the source cited for the wrapped kernel in section 116 of
the parity volume. Section 3, equations (5)–(8) on PDF pp. 3–4,
including the “Wrapped Gaussian series and Jacobi theta functions”
subsection, was inspected. This note cites the preprint and asserts
no journal DOI.

## Classical modulo-one mechanism

The source's model is $X=\mu+(K+\sigma Z)/g$, with $g>0$,
$\sigma>0$, integer-valued $K$ and standard Gaussian read noise.
Reducing $g(X-\mu)$ modulo one removes $K$ exactly. For a phase
$\varphi\in(-\pi,\pi]$, its angular density is

$$
f_\Phi(\varphi)
=\frac1{2\pi\sigma}\sum_{k\in\mathbb Z}
\phi\!\left(\frac{k+\varphi/(2\pi)}{\sigma}\right)
=\frac1{2\pi}\left[1+2\sum_{m\ge1}
e^{-2\pi^2\sigma^2m^2}\cos(m\varphi)\right],
$$

where $\phi$ is the standard normal density. This is equations
(7)–(8), using Poisson summation. The positive periodized Gaussian
has integral one over one angular period. The kernel obtained by
removing $1/(2\pi)$ instead has circle average one; those
normalizations must not be mixed.

## Scope of the parity application

The [spectral-boundary volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
uses the positive wrapped-kernel representation to retain all
half-integer modes and a positive common denominator. A mixture
of positive shifted kernels preserves positivity.

Its empirical center phase $\ell(1/2-\mu_j)$ is not the source's
integer additive signal. The original energy includes data-dependent
centers in a quadratic statistic, so reducing a linear integer
signal modulo one does not remove that phase. The source's
law-invariance, camera-noise conclusions and large-noise uniform
limit do not prove uniformity or anti-concentration of those
posterior centers at fixed model noise. The wrapped-kernel identity
is a classical input; the native arithmetic probability bound has
a separate calibration argument.
