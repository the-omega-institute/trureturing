---
bibkey: zoroa2017couponcollector
authors: N. Zoroa; E. Lesigne; M. J. Fernández-Sáez; P. Zoroa; J. Casas
year: 2017
title: The coupon collector urn model with unequal probabilities in ecology and evolution
doi: 10.1098/rsif.2016.0643
url: https://arxiv.org/abs/1608.00155v1
claim: "The unnumbered conjecture after Definition 8.2 asserts that majorization of risk vectors implies strong stochastic dominance of the number of visited labels."
strata_touched:
  - D5/S3/Analytic/Probability/StrongDominanceRefutation
license: citation-only
triage: anchor
---

# Unequal-probability coupon collection

## Verified locator

DOI: https://doi.org/10.1098/rsif.2016.0643

Source: https://arxiv.org/abs/1608.00155v1

Published full text: https://pmc.ncbi.nlm.nih.gov/articles/PMC5332560/

The arXiv v1 conjecture is on p. 30, after Definition 8.2 on pp. 28 and 30. In the published article the corresponding definition is 7.2.

## Source statements

Section 3, arXiv v1 p. 7:

> Let $Y_n$ be the random variable representing the number of parasitized hosts after $n$ draws, that is $Y_n=k$ if there are exactly $k$ parasitized hosts after $n$ draws.

Definition 8.2, arXiv v1 pp. 28 and 30:

> Let $X$ and $X'$ be two real random variables, defined on probabilities spaces $(\Omega,P)$ and $(\Omega',P')$, respectively, and taking values in a denumerable set $D$. We say that the random variable $X$ strongly stochastically dominates the random variable $X'$ if there is a critical value $c\in\mathbb R$ such that, for any $d\in D$
>
> • if $d\leq c$, then $P(X=d)\leq P'(X'=d)$,
>
> • if $d>c$, then $P(X=d)\geq P'(X'=d)$.

Conjecture, arXiv v1 p. 30:

> If $p\prec q$, then the random variable $Y_n$ defined on the probability space $(\Omega,P_p)$ strongly stochastically dominates the random variable $Y_n$ defined on the probability space $(\Omega,P_q)$.

The source assigns each length-$n$ cylinder the product of its coordinate probabilities. Finite words indexed by `Fin n` and labels indexed by `Fin N` give exactly this marginal; their image cardinality is $Y_n$. The simplex allows zero weights; the counterexample has strictly positive weights. The real threshold has the weak inequality on its lower side. The imported decreasing-prefix majorization includes equal total weights.

## Scope

The source conjectures the one-threshold order and reports the cases $n=2,3$ for all $N$ and $n=4,N\leq5$. The repository result refutes the universal conjecture at $N=4,n=5$. It does not refute the source's proved ordinary stochastic dominance theorem. The bounded literature screen and unverified full-text boundaries are stated in preregistration issue https://github.com/the-omega-institute/trureturing/issues/28951; literature completeness is ASSUMED-UNVERIFIED.

The independent exact checker is in `the-omega-institute/trureturing-experiments`, commit `0e0d1900830295271d2dfbf86b8e53f9c2c69cb0`, path `docs/reports/1608.00155-strong-dominance/check.py`, SHA-256 `f3f435168370f9ff71553778cf56a166d7852ec33bd352275391563e90ee0c53`. Its reported exit code is 0. It supplies computed family and cumulative-distribution evidence; the Lean result supplies the formal refutation.
