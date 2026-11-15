---
bibkey: brent2016evenmoments
authors: Richard P. Brent, Hideyuki Ohtsuka, Judy-anne H. Osborn, Helmut Prodinger
year: 2016
title: Some Binomial Sums Involving Absolute Values
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex
claim: "For every natural r there is an ordinary polynomial P_r in Z[X] such that 2^(4n) P_r(n) = 2^r W_(2r)(n) for every natural n, including both zero indices."
strata_touched:
  - D5/S3/ArithSums/BrentEvenMomentPolynomial
license: citation-only
triage: anchor
---

## Verified locator

Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Brent/brent9.tex

Journal of Integer Sequences 19, Article 16.3.7, section 3.3, printed page 10,
immediately after Theorem 9. The corresponding arXiv version is
[1411.1477v2](https://arxiv.org/abs/1411.1477v2), printed page 11 after Theorem 5.

The source defines

$$
W_\beta(n)=\sum_{i,j=-n}^n
\binom{2n}{n+i}\binom{2n}{n+j}|i^2-j^2|^\beta.
$$

Binomial coefficients are zero outside their valid range and $0^0=1$.
The source proves the weaker coefficient normalization $2^{2r-4n}$, then states:

> It follows from Theorem 9 that the coefficients of $2^{2r-4n}W_{2r}(n)$
> are in $\mathbb Z$, but it is not obvious how to prove the stronger result,
> suggested by the cases above, that the coefficients of $2^{r-4n}W_{2r}(n)$
> are in $\mathbb Z$. We leave this as a conjecture.

The ordinary polynomial assertion concerns integer monomial coefficients,
with the normalization interpreted over the rationals. It requires a single
polynomial for each $r$ that works at every nonnegative $n$.

The source and prior search associated with
[issue 30544](https://github.com/the-omega-institute/trureturing/issues/30544)
is bounded; it supplies no claim of global bibliographic completeness or first discovery.
