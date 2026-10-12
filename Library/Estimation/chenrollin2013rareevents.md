---
bibkey: chenrollin2013rareevents
authors: Louis H. Y. Chen and Adrian Röllin
year: 2013
title: Approximating dependent rare events
doi: 10.3150/12-BEJSP18
url: https://arxiv.org/abs/1306.4158v3
claim: "Section 4 states the Stein–Chen equation and Theorem 4.1 gives the Arratia–Goldstein–Gordon total-variation bound with local dependence and conditional residual terms."
strata_touched: []
license: citation-only
triage: anchor
---

# Stein–Chen approximation and dependence bookkeeping

## Verified locator

DOI: <https://doi.org/10.3150/12-BEJSP18>.
Crossref identifies the title, authors and *Bernoulli* 19(4), 1243–1267.
The [arXiv reprint](https://arxiv.org/abs/1306.4158v3) is accessible;
its 26-page PDF explicitly prints the DOI, journal coordinates and
version stamp 8 October 2013. Section 4, particularly equations
(4.1)–(4.4) and Theorem 4.1 on PDF pp. 4–6, was inspected.

## Classical equation and approximation theorem

For $Z\sim\operatorname{Poisson}(\lambda)$, the Stein equation is

$$
\lambda f(w+1)-wf(w)=h(w)-\mathbb Eh(Z).
$$

The survey attributes the Poisson adaptation to Chen's
*Poisson Approximation for Dependent Trials*, *Annals of Probability*
3(3), 534–545 (1975), DOI
<https://doi.org/10.1214/aop/1176996356>.
That record's metadata is verified; its Project Euclid page returns
an access-control response rather than the article, and Firecrawl
is unavailable with HTTP 402. The present mathematical statement
is checked in the accessible Chen–Röllin reprint.

For Bernoulli variables $X_\alpha$, $p_\alpha=\mathbb EX_\alpha$,
$W=\sum_\alpha X_\alpha$ and $\lambda=\mathbb EW>0$, use
dependence neighborhoods $B_\alpha$ containing $\alpha$ and put

$$
\begin{aligned}
b_1&=\sum_\alpha\sum_{\beta\in B_\alpha}p_\alpha p_\beta,\\
b_2&=\sum_\alpha\sum_{\beta\in B_\alpha\setminus\{\alpha\}}
\mathbb E(X_\alpha X_\beta),\\
b_3&=\sum_\alpha\mathbb E\left|
\mathbb E(X_\alpha\mid X_\beta:\beta\notin B_\alpha)-p_\alpha
\right|.
\end{aligned}
$$

Theorem 4.1, attributed there to Arratia–Goldstein–Gordon, gives

$$
d_{\rm TV}(\mathcal L(W),\operatorname{Poisson}(\lambda))
\le(1\wedge\lambda^{-1})(b_1+b_2)
+(1\wedge1.4\lambda^{-1/2})b_3.
$$

This is the half-variation convention. The term $b_3$ vanishes when
each variable is independent of all variables outside its neighborhood.
An overlapping path does not acquire this property solely from a
one-row marginal calculation.

## Relative atoms and calibrated centers

The theorem controls absolute event errors. Dividing by a small
Poisson point mass can amplify that error, as explained in the
[Le Cam note](lecam1960poissonbinomial.md). Relative tail results
also need their own scale and coupling conditions.

The [parity spectral-boundary model](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
requires uniform relative marked-count probabilities for the actual
pair/path law and a nonlinear posterior mean under shared conditioning.
This survey does not state that native relative-point contract or
the final arithmetic small-ball estimate. Its independent and
dependent rare-event theorems are classical antecedents with
explicit dependence costs.
