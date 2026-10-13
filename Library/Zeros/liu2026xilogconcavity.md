---
bibkey: liu2026xilogconcavity
authors: Yanxin Liu; Jianxi Mao
year: 2026
title: Infinite log-concavity of the Taylor coefficients of the Riemann xi-function
doi: null
url: https://arxiv.org/abs/2610.04972v1
claim: The preprint states unconditional strict infinite log-concavity of the central Taylor coefficients of the Riemann xi-function; it does not supply the Laguerre--Pólya conclusion or a pointwise Robin estimate.
strata_touched: []
license: citation-only
triage: anchor
---

# Infinite log-concavity of the Taylor coefficients of the Riemann xi-function

The source is [arXiv:2610.04972v1](https://arxiv.org/pdf/2610.04972v1), submitted 4 October 2026. The result is a preprint and was not independently audited or formalized here.

## Exact result and logical direction

Write

$$
F(x)=\xi\!\left(\tfrac12+\sqrt{x}\right)=\sum_{n\ge0}\lambda_nx^n,
$$

and let $L$ be the standard log-concavity operator,
$ (La)_n=a_n^2-a_{n-1}a_{n+1}$, with $a_{-1}=0$. Theorem 1.1 states

$$
(L^m\lambda)_n>0\qquad(m,n\ge0).
$$

The paper combines saddle estimates, a two-index recurrence for logarithmic ratios, interval verification for the finite initial range, and a global closure argument. The introduction records the classical implication that RH would put $F$ in the Laguerre--Pólya class and hence imply infinite log-concavity; the new theorem proves the coefficient property without assuming RH.

## Correspondence with the fixed theta measure

To distinguish these coefficients from the prescribed Jensen node parameter,
write $b_j=\lambda_j=\xi^{(2j)}(1/2)/(2j)!$. With the
[Romik source normalization](../Analytic/romik2021orthogonal.md), put

$$
T=x^2/4,\qquad S(T)=\Phi(2\sqrt T),\qquad
d\mu(T)=\frac{2S(T)}{\xi_0\sqrt T}\,dT,\qquad \xi_0=\xi(1/2).
$$

Equations (4.3)–(4.4), printed p.43, give the positive-kernel moment
representation of $b_j$. The paper's kernel in (4.3) is $2\Phi(x)$;
it is not the Csordas-normalized $K(u)$ used in the
[square-variable concavity note](planatsole2026secondlevel.md).
Writing $M_j=\int_0^\infty T^j\,d\mu(T)$ gives the exact correspondence

$$
b_j=\frac{\xi_0\,4^j}{(2j)!}\,M_j.
$$

This is reuse of the source representation in the fixed receiving
coordinate, not an additional coefficient theorem. Theorem 1.1 concerns
the ordinary Taylor coefficients $b_j$. The Jensen convention uses
$\gamma_j=j!b_j$ in the paper's equation (1.1); its factorial multiplier
cannot be discarded when applying an iterated log-concavity conclusion.
The coefficient result does not supply the signed neighboring-row
comparison at every prescribed node or the extra vanishing at common
zeros. Those interfaces remain separate obligations.

## Boundary for Robin and FIB ATOM

The coefficient sequence is a central Taylor expansion of $\xi$, whereas Robin's target is a pointwise divisor-sum inequality. These $\lambda_n$ are not the Li coefficients. The stated result supplies no implication to positivity of all Li coefficients, a zero-free half-plane, or a bound on the same integer's signed Robin tail. Neither this source nor the five-window FIB definitions supply a coefficient-preserving map from $N_g=1+F_rg$ to the Taylor index and coefficient $\lambda_n$.

Reuse the stated coefficient property when its hypotheses and conclusion match the task; it is not a new Robin estimate. Any application to the Robin/FIB route still needs a proved map preserving the actual target and its quantifiers. The preprint does not supply that map.
