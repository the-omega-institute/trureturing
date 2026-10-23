---
bibkey: faveridunnhoffstein2026nonorthogonality
authors: Alexandre de Faveri; Alexander Dunn; Jeffrey Hoffstein
year: 2026
title: "Non-orthogonality of the cubic and quartic large sieves via Rankin--Selberg"
doi: null
url: https://arxiv.org/abs/2607.07911v2
claim: "Theorem 1.1 proves a cubic large-sieve lower bound, Theorem 1.2 proves a quartic lower bound, and Conjecture 1.3 predicts the corresponding obstruction for every fixed order n >= 3; the results identify Gauss-sum bias as an obstruction to perfect orthogonality."
strata_touched: []
license: citation-only
triage: anchor
---

# Gauss-sum bias as a non-orthogonality boundary

The source is [arXiv:2607.07911v2](https://arxiv.org/pdf/2607.07911v2),
updated 13 July 2026. This card records the operator-norm statements and
their relevance to the project's fixed-order character estimates. It is a
literature boundary, not an independent proof audit or Lean certification.

## Proven lower bounds

For the cubic character family, Theorem 1.1 states

$$
\Xi_3(A,B)\gg_\varepsilon (AB)^{-\varepsilon}
\left(A+B+(AB)^{2/3}\right).
$$

For the quartic family, Theorem 1.2 states

$$
\Xi_4(A,B)\gg_\varepsilon (AB)^{-\varepsilon}
\left(A+B+A^{3/4}B^{1/2}+A^{1/2}B^{3/4}\right).
$$

At the balanced scale $A\asymp B\asymp X$, these give respectively
$X^{4/3-\varepsilon}$ and $X^{5/4-\varepsilon}$. Thus the character
families are unconditionally not perfectly orthogonal. The paper attributes
the obstruction to a bias in the relevant Gauss sums and obtains the
quartic input through Rankin--Selberg regularization of metaplectic theta
coefficients.

## General-order prediction

Conjecture 1.3 predicts, for a fixed order $n\ge3$ over a field containing
$\mathbb Q(\zeta_n)$,

$$
\Xi_n(A,B)=(AB)^{o(1)}
\left(A+B+A^{1-1/n}B^{2/n}+A^{2/n}B^{1-1/n}\right)
$$

as $\min(A,B)\to\infty$. For $n=6$ and $A\asymp B\asymp K$, this predicts
the $K^{7/6+o(1)}$ scale appearing in the project's balanced joint-contour
target. The paper does not prove the $n=6$ case or this prediction in general.

## Exact non-overlap with the project's open estimate

The project already records de Faveri's later fixed-order upper bound in
`faveri2026fixedorder.md`. The present source supplies a complementary
lower-bound obstruction:

* it is an operator norm for a full cubic or quartic character family;
* it does not estimate the signed kernel $\mathscr F_{j,a}$ in the joint
  contour target;
* it does not handle the moving quadratic twist coupled to the cubic Gauss
  factor after the project's theta transform; and
* it does not address detector length coverage or the final signed Robin
  restoration.

Consequently the results rule out a diagonal-only or perfect-orthogonality
shortcut, but they are neither an upper bound for (J) nor a Robin or RH
argument. The structural similarity between the paper's Gauss bias and the
project's moving quadratic/cubic coupling is a search interface only; an
explicit reduction would still be a new theorem.

