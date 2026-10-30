---
bibkey: baowangqiu2022ellipticparameter
authors: Q. Bao, M.-K. Wang and S.-L. Qiu
year: 2022
title: "Monotonicity properties of the generalized elliptic integrals with respect to the parameter"
doi: 10.7153/mia-2022-25-64
url: https://arxiv.org/abs/2112.13993
claim: "Open problem 3.5(2) asks for the supremum of the remainder parameter exponent lambda10 for every positive truncation order."
strata_touched:
  - D5/S3/Analytic/EllipticTailExponent/Defs
  - D5/S3/Analytic/EllipticTailExponent/Result
license: citation-only
triage: anchor
---

# Elliptic remainder parameter exponent

## Verified locator

DOI: 10.7153/mia-2022-25-64

Source: https://arxiv.org/abs/2112.13993

Pinned version: https://arxiv.org/abs/2112.13993v1, equations (3.2)
and (3.6), Lemma 3.2(4), Remark 3.4 and Open problem 3.5(2).
The journal version is *Mathematical Inequalities & Applications*
25(4) (2022), 1021–1045.

## Mathematical correspondence

With $(a)_k=\prod_{j=0}^{k-1}(a+j)$, equation (3.2) at $c=1$ gives
$g_{6,k}(a)=a(a)_k(1-a)_k$. Put

$$S_n(a)=\sum_{k=0}^n\frac{g_{6,k}(a)}{(k+1)(k!)^2}.$$

Equation (3.6) defines

$$\lambda_{10}(a)=\frac{a}{1-a}
\frac{\sin(\pi a)+\pi(1-a)\cos(\pi a)-\pi(1-a)^2S_n'(a)}
{\sin(\pi a)-\pi(1-a)S_n(a)}.$$

`Defs.g6`, `Defs.S` and `Defs.lambda10` in
`D5/S3/Analytic/EllipticTailExponent/Defs` encode these real functions,
including the ordinary real derivative of the finite polynomial.
`Defs.claim` asserts that two is the least upper bound of the exponent
values on $(0,1/2]$ for every natural $n$, including zero.
`D5/S3/Analytic/EllipticTailExponent/Result.result` proves this claim.
Lemma 3.2(4) settles $n=0$; Open problem 3.5(2) asks for the general value.

The literature scope and the distinction between the formal result and
its further consequences are stated in
`Problems/bao-wang-qiu-2022-elliptic-tail-exponent.md`.
