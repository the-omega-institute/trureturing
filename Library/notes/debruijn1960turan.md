---
bibkey: debruijn1960turan
authors: N. G. de Bruijn
year: 1960
title: "On Turán's first main theorem"
doi: 10.1007/BF02020939
claim: "Sections 3–5: a sequence satisfying a linear recurrence of order m with characteristic roots in |z|≤θ satisfies |x_{m+r}|≤ε θ^{r+1} sum_{j<m} C(r+j,j)(1+θ)^j when |x_k|≤ε for 0≤k<m. For 0≤θ<1, summation gives the absolute tail bound (ε/2)[((1+θ)/(1−θ))^m−1]."
strata_touched: []
license: citation-only
triage: anchor
---

# Turán's first main theorem and an absolute tail bound

Let $m\ge1$ and let $(x_n)_{n\ge0}$ satisfy a linear recurrence of order $m$
whose characteristic roots lie in $|z|\le\theta$. If $\epsilon\ge0$ and
$|x_k|\le\epsilon$ for $0\le k<m$, the estimate in §§3–5 gives

$$
|x_{m+r}|\le
\epsilon\theta^{r+1}
\sum_{j=0}^{m-1}\binom{r+j}{j}(1+\theta)^j
\qquad(r\ge0).
$$

For $0\le\theta<1$, summing the binomial generating functions
$\sum_{r\ge0}\binom{r+j}{j}\theta^r=(1-\theta)^{-j-1}$ yields

$$
\sum_{n\ge m}|x_n|
\le\frac\epsilon2
\left[\left(\frac{1+\theta}{1-\theta}\right)^m-1\right].
$$

Adding the first $m$ terms gives

$$
\sum_{n\ge0}|x_n|
\le\epsilon\left\{
m+\frac12\left[\left(\frac{1+\theta}{1-\theta}\right)^m-1\right]
\right\}.
$$

Thus the absolute tail constant follows directly from the published estimate.

## Verified locator

- N. G. de Bruijn, *On Turán's first main theorem*, Acta Mathematica Academiae Scientiarum Hungaricae 11(3–4) (1960), 213–216.
- DOI: https://doi.org/10.1007/BF02020939
- Result locator: §§3–5; the recurrence estimate above is expressed with an initial block indexed by $0,\ldots,m-1$.
