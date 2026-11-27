---
bibkey: montgomery1988minimal
authors: H. L. Montgomery
year: 1988
title: Minimal theta functions
doi: 10.1017/S0017089500007047
url: https://doi.org/10.1017/S0017089500007047
claim: Main theorem: for every positive parameter, among positive definite binary quadratic forms of fixed discriminant the theta function sum over integer pairs of exp(-pi t form) is minimized by the hexagonal form, with equality only for forms integrally equivalent to it.
strata_touched:
  - D5/S3/Fourier/HexagonalThetaMinimum
  - D5/S3/Fourier/ThetaLatticeMinimum
  - D5/S3/Fourier/EpsteinMellinMinimum
license: citation-only
triage: anchor
---

# Minimal theta functions

The article is H. L. Montgomery, Glasgow Mathematical Journal 30 (1988),
75–85, available through the [DOI](https://doi.org/10.1017/S0017089500007047).
Its publisher abstract recalls that Rankin, Cassels, Ennola and Diananda
between them proved the hexagonal minimum of the Epstein zeta function for
every real $s>0$, and states that the paper proves the corresponding result
for theta functions.

The main theorem, as restated in M. Bétermin and M. Faulhuber, *Maximal
theta functions*, [arXiv:2007.15977](https://arxiv.org/abs/2007.15977),
Theorem 1.4: for every $\alpha>0$ and every positive definite binary
quadratic form $q$ of the fixed discriminant, $\theta_h(\alpha)\le
\theta_q(\alpha)$, where $h$ is the form of the hexagonal lattice, with
equality if and only if $q$ is integrally equivalent to $h$.

In the Lean convention, a unit-covolume lattice in reduced coordinates is
given by the determinant-one form
$Q_{x,y}(m,n)=((m+nx)^2+y^2n^2)/y$ with $y>0$, and the theta series is
$F_t(x,y)=\sum_{(m,n)\in\mathbb Z^2}e^{-\pi t\,Q_{x,y}(m,n)}$ for $t>0$.
The hexagonal point is $(x,y)=(1/2,\sqrt3/2)$. Integral equivalence of forms
corresponds to equality of lattices up to a real orthogonal map, rotations
and reflections included. The explicit intermediate estimates and their
constants in the Lean development are separate derivations; this note does
not assert that each of them appears in the article.

## Verified locator

- URL: https://doi.org/10.1017/S0017089500007047
- DOI: 10.1017/S0017089500007047
