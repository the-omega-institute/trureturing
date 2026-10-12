---
bibkey: nguyenvu2013smallball
authors: Hoi H. Nguyen and Van H. Vu
year: 2013
title: Small ball probability, Inverse theorems, and applications
doi: 10.1007/978-3-642-39286-3_16
url: https://arxiv.org/abs/1301.0019v1
claim: "The survey reviews concentration of independent random linear combinations and inverse Littlewood–Offord theorems that associate large concentration with additive structure."
strata_touched: []
license: citation-only
triage: anchor
---

# Small-ball theorems and the missing native posterior interface

## Verified locator

DOI: <https://doi.org/10.1007/978-3-642-39286-3_16>.
Crossref identifies the published chapter in *Erdős Centennial*
(2013), pp. 409–463. The consumed text is the prepublication version.
The [arXiv record](https://arxiv.org/abs/1301.0019v1) and its 47-page
PDF are accessible with HTTP 200 and identify Nguyen, Vu and this
title. The record's sole version is submitted 31 December 2012;
this differs from the chapter's publication year. The independent-summand setup and Theorems
1.1–1.2 on PDF pp. 2–3, the fixed-dimension discussion in section 2,
and the bibliography were inspected.

## Classical direct and inverse questions

The basic object is $S_A=\sum_i a_i\xi_i$, with deterministic
coefficients and independent copies of a specified random variable.
A concentration probability is the largest mass of a ball of a
given radius. For fair signs and real $|a_i|\ge1$, Theorem 1.2
records the sharp bound
$2^{-n}\binom n{\lfloor n/2\rfloor}$ for an open interval of length
two, credited to [Erdős](erdos1945littlewoodofford.md).

The inverse problem asks what coefficient structure is forced by a
large concentration probability. It does not assume that arbitrary
coefficients give a fine-scale density approximation. The paper
separately treats linear, bilinear and quadratic forms; their
coefficient and randomness hypotheses must be retained.
Its bibliography locates Rogozin's *An Estimate for Concentration
Functions* (1961) and Esséen's Kolmogorov–Rogozin work (1966).

## Original conditional arithmetic small ball

The target in the
[parity spectral-boundary volume](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
is the conditional probability that
$\ell(1/2-\mu_0)$ is within $\tau$ of an integer, for each fixed
nonzero integer $\ell$. Here $\mu_0$ is a complete fixed-size
posterior group mean. The varying rectangle count has a
hypergeometric conditional law; its posterior calibration and shared
denominator move with that count.

The model's estimate has the form

$$
\mathbb P\!\left(
\operatorname{dist}(\ell(1/2-\mu_0),\mathbb Z)\le\tau
\mid\mathrm{Env}\right)
\le C_\ell\left[L(s+\tau)
+\frac{1+\tau/s}{\sqrt N}+L^{-2}\right].
$$

Its native environment, positive conditional mass, good-environment
exceptional budget, original decimal amplitude and common scale
$s\asymp N/q$ are part of the application. This relationship is a
repository derivation; no theorem in the inspected survey supplies
those hypotheses and conclusion together. Independent linear-sum
results and the classical inverse-square-root order are antecedents,
not a direct identification with the nonlinear posterior statistic.
This comparison does not certify global originality or by itself
settle the volume's remaining spectral-limit implication.
