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

and regularizes them by Mellin convolution. Theorem 8.1 fixes the polynomially
damped net of Section 4, with
$\delta(\varepsilon)=(\log(1/\varepsilon))^{-\alpha}$, $0<\alpha<1$,
and $n(\varepsilon)=\lfloor\varepsilon^{-M}\rfloor$, $M>0$.
It states that RH holds exactly when this net is moderate, associated with
$-\iota(\mathbf1_{(0,1)})$, and uniformly bounded in $L^2(0,1)$.
The minus sign belongs to this specified Möbius convention. The converse is
obtained through the classical Nyman--Beurling criterion and Mazur's theorem.
The separate power-law estimate in Theorem 9.1 assumes RH as well as simplicity
and the stated separation condition for the nontrivial zeros; the paper leaves
stronger exponential damping as an open problem.

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
