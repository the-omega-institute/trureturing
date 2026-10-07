---
bibkey: verjovsky2026mobiussmoothing
authors: Alberto Verjovsky
year: 2026
title: "How Random Is the Möbius Function? Smoothing, Probability, and the Riemann Hypothesis"
doi: null
url: https://arxiv.org/abs/2607.25002v2
claim: "Theorem 3.1 states the Möbius Laplace Lp criterion for every 1≤p<2; Proposition 2.2 gives the zero-free half-plane from one exponent. The actual FIB multiplier is an invertible dilation filter, not an unconditional membership proof."
strata_touched: []
license: citation-only
triage: anchor
---

# The existing smoothed Möbius criterion and its FIB filter

The primary version is [arXiv:2607.25002v2](https://arxiv.org/abs/2607.25002v2),
submitted 14 August 2026, 28 pages. The inspected original scope is
Sections 2–3: Propositions 2.1–2.2, Theorem 3.1 and Remarks 3.2–3.3.
The selected proofs were read; the rest of the manuscript and its
probabilistic and dynamical interpretations are not independently audited.
No Lean verification or original FIB criterion is asserted.

For

$$
\Phi_\mu(t)=\sum_{n\ge1}\mu(n)e^{-nt},\qquad t>0,
$$

Proposition 2.1 gives the classical Mellin transform
$\int_0^\infty\Phi_\mu(t)t^{s-1}dt=\Gamma(s)/\zeta(s)$ for $\Re s>1$.
Proposition 2.2 states that one $L^p(0,\infty)$ bound, $1<p<\infty$,
implies $\zeta(s)\ne0$ on $\Re s>1/p$. Theorem 3.1 states

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\Phi_\mu\in L^p(0,\infty)\ \text{for every }1\le p<2.
$$

Remark 3.2 explicitly excludes an endpoint assertion at $p=2$.
A fixed exponent below two does not give the full criterion, and a random
coefficient statement is not a statement about the deterministic Möbius
sequence.

The actual FIB coefficients satisfy $e=\mu*\beta$, with
$\beta_n=\log(1-(-\varphi^{-2})^n)$ and the already established
absolutely summable inverse $\gamma=\beta^{-1}$. Define
$\Phi_e(t)=\sum_{n\ge1}e_ne^{-nt}$. Absolute convergence at every $t>0$
and the existing convolution identities give the two dilation formulas

$$
\Phi_e(t)=\sum_{d\ge1}\beta_d\Phi_\mu(dt),\qquad
\Phi_\mu(t)=\sum_{d\ge1}\gamma_d\Phi_e(dt).
$$

These are applications of the established filter, not new analytic
criteria. The standard dilation norm $\|g(d\,\cdot)\|_p=d^{-1/p}\|g\|_p$
and the triangle inequality give, whenever the right side is finite,

$$
\|\Phi_e\|_p\le\left(\sum_d|\beta_d|d^{-1/p}\right)\|\Phi_\mu\|_p,
\qquad
\|\Phi_\mu\|_p\le\left(\sum_d|\gamma_d|d^{-1/p}\right)\|\Phi_e\|_p.
$$

Both filter constants are finite by the existing FIB inverse budget.
Thus the source supplies a reusable alternative test for the same actual
arithmetic input. It does not supply the still missing $L^p$ membership
for all exponents below two, a signed Robin bound, or a geometric rule
that forces either. This adaptation has no new retained Lean wrapper.
