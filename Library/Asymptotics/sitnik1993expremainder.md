---
bibkey: sitnik1993expremainder
authors: S. M. Sitnik
year: 1993
title: Inequalities for the exponential remainder of the Taylor series
doi: null
url: https://arxiv.org/abs/1608.08784
claim: "Problem 11 conjectures positivity of every positive-order forward difference of the consecutive exponential Taylor remainder ratio at each positive argument."
strata_touched:
  - D5/S3/Analytic/ExpRemainderDifferences
license: citation-only
triage: anchor
---

# Exponential remainder ratio differences

## Verified locator

Source: https://arxiv.org/abs/1608.08784

Pinned version: https://arxiv.org/abs/1608.08784v2.
The original work is the Vladivostok preprint of 1993, titled
*Неравенства для остатка ряда Тейлора экспоненты*; the arXiv version
includes a supplement from 2016. The locator is the appendix
(Дополнение), additional problem list, Problem 11, PDF pages 27–28.
The remainder notation is equation (1); the first-difference inequality
is equation (42) in Theorem 8.

## Problem 11: source and translation

> 11. Определим функцию при x > 0. gₙ(x) = Rₙ₋₁(x)/Rₙ(x). Исследовать, при каких k разности этой функции при любом фиксированном x неотрицательны ∆ᵏgₙ(x) > 0? Гипотеза: при любых k. При k = 1 гипотеза сводится к (42), при k = 2 к неравенству задачи 1 на стр. 20.

Translation: For $x>0$, define $g_n(x)=R_{n-1}(x)/R_n(x)$.
Investigate for which $k$ the differences of this function, at every
fixed $x$, are nonnegative, $\Delta^k g_n(x)>0$.
Conjecture: for all $k$. For $k=1$ the conjecture reduces to (42),
and for $k=2$ to the inequality of Problem 1 on page 20.

## Mathematical correspondence

Equation (1) defines

$$R_n(x)=e^x-\sum_{j=0}^{n}\frac{x^j}{j!},\qquad x\ge0.$$

`ExpRemainderDifferences.R` is precisely this finite-sum expression over
the reals. `g` is $R_{n-1}/R_n$, used at $n\ge1$ and $x>0$.
The forward difference is in the index $n$, with positive unit step:

$$\Delta^k g_n(x)=\sum_{j=0}^{k}(-1)^{k-j}\binom{k}{j}g_{n+j}(x).$$

The source calls the differences nonnegative but displays a strict
inequality. `claim` uses the weaker nonnegative assertion, universally
over $k\ge1$, $n\ge1$ and $x>0$, with Mathlib's iterated `fwdDiff`.
The negative third difference at $(n,x)=(1,1)$ contradicts both readings.
`result` states exactly the negation of `claim`.

Equation (42), $R_n^2>R_{n-1}R_{n+1}$, gives the case $k=1$.
The source identifies $k=2$ with Problem 1; the follow-up
reference is K. Mehrez and S. M. Sitnik (2014),
https://arxiv.org/abs/1410.6120.
The bibliographic scope and unresolved ranges are stated in
`Problems/sitnik-1993-exponential-remainder-differences.md`.
