---
bibkey: sen1999geometricconvolution
authors: A. Sen; N. Balakrishnan
year: 1999
title: "Convolution of geometrics and a reliability problem"
doi: 10.1016/S0167-7152(98)00284-3
claim: "Theorem 1 gives the distribution of a sum of independent non-identical geometric variables. For positive-integer summands with success probabilities 1−λ_i and distinct 0<λ_i<1, its survival function is P(T>n)=sum_i c_i λ_i^n, where c_i=product_{l≠i}(1−λ_l)/(λ_i−λ_l); hence P(T>n)=1 for 0≤n<q, where q is the number of summands."
strata_touched: []
license: citation-only
triage: anchor
---

# Geometric convolution and an initial survival plateau

For independent geometric variables supported on the positive integers, write

$$
\Pr(G_i=k)=(1-\lambda_i)\lambda_i^{k-1},\qquad
T=\sum_{i=1}^qG_i,
\qquad 0<\lambda_i<1,
$$

with pairwise distinct parameters. Theorem 1 yields the geometric-convolution
distribution. In this convention its survival form is

$$
\Pr(T>n)=\sum_{i=1}^q c_i\lambda_i^n,
\qquad
c_i=\prod_{\ell\ne i}\frac{1-\lambda_\ell}{\lambda_i-\lambda_\ell}
\quad(n\ge0).
$$

This expression is a survival probability. The corresponding probability mass is

$$
\Pr(T=n)=\sum_{i=1}^q c_i(1-\lambda_i)\lambda_i^{n-1}
\quad(n\ge1).
$$

Since every summand is at least one, the survival probability equals one for
$0\le n<q$ and lies in $[0,1]$ for every $n\ge0$. The tail-sum identity gives

$$
\sum_{n\ge0}\Pr(T>n)=\mathbb ET
=\sum_{i=1}^q\frac1{1-\lambda_i}.
$$

## Verified locator

- A. Sen and N. Balakrishnan, *Convolution of geometrics and a reliability problem*, Statistics & Probability Letters 43(4) (1999), 421–426.
- DOI: https://doi.org/10.1016/S0167-7152(98)00284-3
- Result locator: Theorem 1; the formulas above use positive-integer geometric waiting times and express the resulting survival function.
