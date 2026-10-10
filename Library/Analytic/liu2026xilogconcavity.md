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

## Boundary for Robin and FIB ATOM

The coefficient sequence is a central Taylor expansion of $\xi$, whereas Robin's target is a pointwise divisor-sum inequality. These $\lambda_n$ are not the Li coefficients. The stated result supplies no implication to positivity of all Li coefficients, a zero-free half-plane, or a bound on the same integer's signed Robin tail. Neither this source nor the five-window FIB definitions supply a coefficient-preserving map from $N_g=1+F_rg$ to the Taylor index and coefficient $\lambda_n$.

Reuse the stated coefficient property when its hypotheses and conclusion match the task; it is not a new Robin estimate. Any application to the Robin/FIB route still needs a proved map preserving the actual target and its quantifiers. The preprint does not supply that map.
