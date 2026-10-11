---
bibkey: alvarezcruz2026colombeau
authors: Amaury Alvarez Cruz; Esteban A. Alvarez Gutierrez
year: 2026
title: Multiplicative Colombeau algebras and the Nyman--Beurling criterion for the Riemann hypothesis
doi: null
url: https://arxiv.org/abs/2606.22562v3
claim: The preprint reformulates the Báez--Duarte/Nyman--Beurling criterion using multiplicative Colombeau nets; it does not add an arithmetic estimate or prove RH.
strata_touched: []
license: citation-only
triage: anchor
---

# A multiplicative Colombeau formulation of Nyman--Beurling

The inspected source is [arXiv:2606.22562v3](https://arxiv.org/pdf/2606.22562v3),
updated 29 September 2026 and first posted on 21 June 2026, according to the
versioned arXiv metadata. The manuscript heading says May 2025; that is not
the arXiv posting date. Its theorem
statements are recorded as literature input; the proof was not independently
audited here, and no Lean verification is claimed.

The source forms polynomially damped Báez--Duarte sums

$$
f_{\delta,n}(x)=\sum_{k\le n}\mu(k)k^{-\delta}\,\{1/(kx)\}
$$

and regularizes them by Mellin convolution. Its main equivalence says that RH
holds exactly when a corresponding moderate Colombeau net is associated with
the characteristic function of $(0,1)$ and is uniformly bounded in $L^2$.
The converse is obtained through the classical Nyman--Beurling criterion and
Mazur's theorem. A separate power-law estimate is conditional on simplicity
and separation of the nontrivial zeros; the paper leaves stronger exponential
damping as an open problem.

## Boundary for the FIB route

This source supplies a modern analytic completion of the discrete Möbius
approximation criterion. It does not identify the project's FIB five-window
addresses, affine family $1+F_rg$, or four-phase operator with the Beurling
generators, and it supplies no bound for $\sigma(N_g)/N_g$. The Mellin
regularization therefore cannot be applied to the FIB geometry without a new
source-preserving embedding and a proof that the induced coefficients are the
same Möbius coefficients.

The reusable interface is the separation between association and uniform
$L^2$ boundedness. Any FIB-to-Nyman construction must prove both properties;
pointwise convergence of a FIB projection alone is insufficient.
