---
bibkey: karnikrombergdavenport2021prolate
authors: Santhosh Karnik, Justin Romberg, Mark A. Davenport
year: 2021
title: Improved bounds for the eigenvalues of prolate spheroidal wave functions and discrete prolate spheroidal sequences
doi: 10.1016/j.acha.2021.04.002
url: https://arxiv.org/abs/2006.00427v2
claim: Explicit prolate concentration eigenvalue and trace-tail bounds give effective finite-rank errors for that operator. The physical prolate and additive Weil-band parameters differ, and neither bound supplies an actual-Weil finite-section error or arithmetic positivity.
strata_touched: []
license: citation-only
triage: anchor
---

# Effective concentration bounds and the operator interface

The primary text inspected is [arXiv:2006.00427v2](https://arxiv.org/pdf/2006.00427v2), associated with *Applied and Computational Harmonic Analysis* 55 (2021), 97–128, DOI [10.1016/j.acha.2021.04.002](https://doi.org/10.1016/j.acha.2021.04.002). The 29-page PDF SHA-256 is `7c56255db5bd6454e3fc926952052fe466ffd49c4961ad8206638dcac1dd39a0`. Section 2.2 and Corollaries 3–4, printed pp.3–4 and p.9, specify the operator, Fourier convention, constants and index ranges. The bounds are reused as source results; their proofs and numerical experiments are not reproduced here.

## Explicit source bounds

Write $\gamma$ for the source's concentration parameter, reserving $c$ for the project's prime-power cutoff. On $L^2([-1,1])$, use the sinc concentration operator

$$
(S_\gamma h)(x)=\int_{-1}^1
\frac{\sin(\gamma(x-y))}{\pi(x-y)}h(y)\,dy.
$$

Its decreasing eigenvalues are indexed from zero. Define

$$
b_\gamma=\frac2{\pi^2}\log(100\gamma/\pi+25),
\qquad m_\gamma=\lceil2\gamma/\pi\rceil.
$$

The upper half of Corollary 3 states

$$
\mu_k(\gamma)\le
10\exp\bigl(-(k-m_\gamma-6)/b_\gamma\bigr),
\qquad k\ge m_\gamma.
$$

Corollary 4 states

$$
\sum_{k=K}^\infty\mu_k(\gamma)\le
10b_\gamma\exp\bigl(-(K-m_\gamma-7)/b_\gamma\bigr),
\qquad K\ge m_\gamma.
$$

These are effective bounds with explicit constants, rather than fixed-mode asymptotics. Retaining modes $0,\ldots,K-1$ of this same operator gives an operator-norm error bounded by the first omitted eigenvalue and a trace-norm error bounded by the displayed sum. In particular, for $0<\varepsilon<1$, the source's eigenvalue bound supplies an operator-norm allowance $\varepsilon$ when the integer $K$ satisfies

$$
K\ge m_\gamma+6+b_\gamma\log(10/\varepsilon).
$$

This spectral truncation uses concentration eigenmodes. It is not a statement about an arbitrary retained polynomial or trigonometric basis.

## Two parameter maps that must remain distinct

In the source's angular-frequency convention $e^{-i\omega t}$, a physical interval $[-T/2,T/2]$ and band $[-\Omega,\Omega]$ have $\gamma=\Omega T/2$.

| Construction | Physical half-width | Angular-frequency band | Concentration parameter |
|---|---:|---:|---:|
| Connes physical prolate window, Fourier convention $e^{2\pi ixy}$ | $\lambda$ | $2\pi\lambda$ | $2\pi\lambda^2=2\pi c$ |
| Project's additive Weil-band window | $L=\log\lambda$ | $\Omega$ | $\Omega\log\lambda$ |

For the first construction the finite-rank allowance above reads

$$
K\ge\lceil4c\rceil+6+
\frac2{\pi^2}\log(200c+25)\log(10/\varepsilon).
$$

For the second construction, substitute $\gamma=\Omega L$ in the source bound instead. Neither substitution identifies the two physical spaces or their retained bases.

## What still needs an actual-Weil estimate

The [2026 spectral source](connesconsanimoscovici2026spectral.md) already supplies the auxiliary transform convergence. Applying the present concentration bounds to that auxiliary operator does not bound the difference from its actual Weil ground eigenfunction. That needs a quantitative arithmetic transport, a common norm and the specified normalization.

For the [existing retained Weil comparison](liu2026tailcompensation.md), the modes are even Legendre polynomials in the additive window. An error bound in concentration eigenmodes cannot be assigned to that projection without a justified basis comparison. More generally, concentration-operator norm control does not pay for the actual Gamma, prime translations, poles or their couplings to the discarded test space. The unresolved finite-section allowance $r(L,N)$ concerns the full common form, not $S_\gamma$.

No new eigenvalue experiment, actual-Weil lower bound, kernel verification or RH proof is provided by this source note. Its reusable contribution is the explicit concentration error supplier with its correct operator and parameters.
