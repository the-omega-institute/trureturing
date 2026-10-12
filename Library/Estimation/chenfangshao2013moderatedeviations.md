---
bibkey: chenfangshao2013moderatedeviations
authors: Louis H. Y. Chen, Xiao Fang and Qi-Man Shao
year: 2013
title: "Moderate deviations in Poisson approximation: a first attempt"
doi: 10.5705/ss.2012.203s
url: https://arxiv.org/abs/1207.1605v3
claim: "Theorem 2.3 of the arXiv version gives relative right-tail Poisson approximation under a size-biased coupling and explicit conditional jump bounds; it does not assert a uniform relative point-mass bound."
strata_touched: []
license: citation-only
triage: anchor
---

# Relative Poisson tails and point-mass amplification

## Verified locator

DOI: <https://doi.org/10.5705/ss.2012.203s> identifies Chen, Fang and
Shao's paper in *Statistica Sinica* 23, 1523–1540. The journal PDF
prints 2013; Crossref records 2014. The citation year follows the
printed journal volume. The publisher's HTTPS certificate chain is
not validated by the available client, so the mathematical statement
below is checked in the securely accessible
[arXiv version](https://arxiv.org/abs/1207.1605v3), HTTP 200.
Its 21-page PDF has version stamp 20 June 2013. Definition 2.1,
Theorems 2.2–2.3 and equations (2.5)–(2.10), on PDF pp. 4–5,
were inspected. Numbering below refers to that version; the journal
labels the relative-tail theorem Theorem 3 on printed p. 1527.

## Classical size-biased relative-tail theorem

Let $W$ be a nonnegative integer-valued random variable with
$\mathbb EW=\lambda>0$. A variable $W^s$ has the $W$-size-biased
law when $\mathbb E[Wf(W)]=\lambda\mathbb E[f(W^s)]$ for all
functions with existing expectations. Couple $W^s$ and $W$ on the
same probability space and suppose

$$
\Delta=W+1-W^s\in\{-1,0,1\},\qquad
\mathbb P(\Delta=-1\mid W)\le\delta_1,\qquad
\mathbb P(\Delta=1\mid W)\le\delta_2W
$$

almost surely, for nonnegative constants $\delta_1,\delta_2$.
For $Z\sim\operatorname{Poisson}(\lambda)$ and an integer
$k\ge\lambda$, put $\xi=(k-\lambda)/\sqrt\lambda$.
There are absolute positive constants $c,C$ such that

$$
(\delta_1+\delta_2\lambda)(1+\xi^2)\le c
\quad\Longrightarrow\quad
\left|\frac{\mathbb P(W\ge k)}{\mathbb P(Z\ge k)}-1\right|
\le C(\delta_1+\delta_2\lambda)(1+\xi^2).
$$

These are right-tail probabilities in a specified moderate-deviation
range. Existence of a size-biased law alone does not establish the
coupling's jump or conditional-probability bounds.

## Boundary for the native marked-count contract

If relative tail errors at both $k$ and $k+1$ are at most $\varepsilon$,
subtracting tails supplies only

$$
\left|\frac{\mathbb P(W=k)}{\mathbb P(Z=k)}-1\right|
\le\varepsilon\,
\frac{\mathbb P(Z\ge k)+\mathbb P(Z\ge k+1)}{\mathbb P(Z=k)}.
$$

The amplification factor and both range conditions must be retained.
This is a different boundary from the absolute variation errors in
the [Le Cam](lecam1960poissonbinomial.md) and
[Stein–Chen survey](chenrollin2013rareevents.md) notes.

The [parity spectral-boundary model](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md)
uses uniform relative one- and two-row atoms of the actual pair/path
history law under shared conditioning. This theorem does not supply
that joint law, its required coupling, or its small-count range.
It also does not state the nonlinear posterior center's conditional
modulo-one small-ball estimate. It supplies a classical relative-tail
antecedent with explicit conditions, rather than the native contract.
