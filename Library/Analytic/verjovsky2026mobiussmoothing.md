---
bibkey: verjovsky2026mobiussmoothing
authors: Alberto Verjovsky
year: 2026
title: "How Random Is the Möbius Function? Smoothing, Probability, and the Riemann Hypothesis"
doi: null
url: https://arxiv.org/abs/2607.25002v2
claim: "Theorem 3.1 states the Möbius Laplace Lp criterion for every 1≤p<2; Proposition 2.2 gives the zero-free half-plane from one exponent. Corollary 9.3 supplies a conditional fixed-fourth-moment input for the original Robin functional. The FIB filter supplies neither bound."
strata_touched: []
license: citation-only
triage: anchor
---

# The existing smoothed Möbius criterion and its FIB filter

The primary version is [arXiv:2607.25002v2](https://arxiv.org/abs/2607.25002v2),
first submitted 27 July 2026, revised 14 August 2026, 28 pages. The
inspected scope comprises Sections 2–3: Propositions 2.1–2.2, Theorem 3.1
and Remarks 3.2–3.3, and Section 9 as specified below. The selected
proofs were read; the rest of the manuscript and its
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

## A fixed local fourth-moment input for the original Robin functional

For this application the inspected primary scope also includes Section 9,
Lemma 9.1, Proposition 9.2 and Corollary 9.3, equations (8)--(11),
and Remark 9.4 of the same version. Its moment-to-point-value result is
used directly, without re-proving it. These are preprint inputs and
ordinary analytic parameter substitutions, without Lean certification
or a new mathematical-priority claim.

For the actual deterministic Möbius sequence, set
$$
S_N(t)=\sum_{n\le N}\mu(n)e^{2\pi int},\qquad
\mathcal M_{4,c}(N)=\left[
\frac N{2c}\int_{-c/N}^{c/N}|N^{-1/2}S_N(t)|^4\,dt
\right]^{1/4},\qquad c>0\ \text{fixed}.
$$
The arc shrinks with the original cutoff $N$; there is no average over
other cutoffs or substitution of a random coefficient law.
Corollary 9.3 at $q=4$ supplies exactly
$$
|M(N)|\ll_c
\max\left(N^{1/2}\mathcal M_{4,c}(N),
          N^{3/5}\mathcal M_{4,c}(N)^{4/5}\right).
$$
Consequently the additional bound
$\mathcal M_{4,c}(N)\ll N^\nu$ for one fixed $0\le\nu<1/32$
and every sufficiently large $N$ gives
$M(N)\ll N^\vartheta$, where
$$
\vartheta=\frac35+\frac45\nu<\frac58.
$$
The other branch $1/2+\nu$ is smaller since $\nu<1/2$.
The [original-functional application (I118)--(I119)](../Weil/corvalan2023interpolation.md#a-fixed-mertens-input-sufficient-for-the-original-functional)
then gives $\mathscr J_N(R_N)=o(1)$, using
$\vartheta<\beta<5/8$ to retain the needed prime-error input as well
as the actual short band and endpoint. The moment hypothesis is not
proved by Corollary 9.3; it is precisely an unpaid deterministic input.

There is an exact finite correlation version of the same input. Define
$\operatorname{sinc}(u)=\sin(\pi u)/(\pi u)$ for $u\ne0$, with
$\operatorname{sinc}(0)=1$, and
$$
\mathfrak C_{4,c}(N)=
\sum_{n_1,n_2,n_3,n_4\le N}
\mu(n_1)\mu(n_2)\mu(n_3)\mu(n_4)
\operatorname{sinc}\!\left(
\frac{2c(n_1+n_2-n_3-n_4)}N\right).
$$
All four indices run over positive integers. Finite expansion of the
moment integral gives, with its normalization unchanged,
$$
\mathfrak C_{4,c}(N)=N^2\mathcal M_{4,c}(N)^4\ge0.
$$
The nonnegativity is for the complete integral, not for each signed
correlation summand. In particular a further hypothetical bound
$\mathfrak C_{4,c}(N)\ll N^{17/8-\xi}$ for fixed $0<\xi\le1/8$
gives $\vartheta=5/8-\xi/5$. Allowing the strict exponent slack in
(I119), for every fixed $\eta>0$ this would imply
$$
|\mathscr J_N(R_N)|\ll_{c,\xi,\eta}N^{-2\xi/5+\eta}.
$$
Choose $\eta<2\xi/5$ for decay. This formulation does not prove the
correlation bound or replace the fourfold joint sum by its diagonal.

One fixed fourth moment suffices for this particular functional under
the displayed hypothesis. It does not supply the paper's RH criterion,
which requires control for unbounded moment orders, or the complete
signed Robin inequality. The existing FIB dilation-filter equivalence
above still supplies no deterministic moment estimate. The application
preserves the original Möbius input and makes no inference from a
measure-typical random model to that single sequence.
