---
bibkey: puccettiwang2015dependence
authors: Giovanni Puccetti and Ruodu Wang
year: 2015
title: Extremal Dependence Concepts
doi: 10.1214/15-STS525
url: https://arxiv.org/abs/1512.03232v3
claim: "Bivariate distributions with fixed marginals have sharp lower and upper Frechet-Hoeffding bounds, attained by countermonotonic and comonotonic couplings."
strata_touched:
  - D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope
license: citation-only
triage: anchor
---

# Fixed marginals, sharp couplings and target dependence

Giovanni Puccetti and Ruodu Wang, *Extremal Dependence Concepts*,
Statistical Science 30(4), 485–517. The directly consumed author text
is arXiv:1512.03232v3.

Section 1 distinguishes the joint distribution from its one-dimensional
marginals and defines the Fréchet class. Section 2, Theorem 2.1(b),
gives the comonotonic joint distribution
$F^{\vee}_2(u,v)=\min(F_1(u),F_2(v))$.
Section 3.1, Theorem 3.1(b), equation (3.2), gives the countermonotonic
distribution $F^{\wedge}_2(u,v)=\max(F_1(u)+F_2(v)-1,0)$.
Equation (3.5) states the sharp bivariate ordering between them.
The original author PDF's pp. 11–12 contain these lower-bound clauses.
These are classical bounds reviewed by the authors, not results newly
attributed to this repository or priority claims about their discovery.

For two Bernoulli events $A,B$ with probabilities $u,v$, let
$k=P(A\cap B)$. Their four-cell law is

$$
(p_{00},p_{10},p_{01},p_{11})
=(1-u-v+k,u-k,v-k,k).
$$

Nonnegativity is equivalent to
$\max(0,u+v-1)\le k\le\min(u,v)$; each endpoint is attainable.
This is the finite-event application of the bivariate bounds. If an
additional disjoint mode has probability $Z$, condition on its complement
of mass $r=1-Z>0$ and substitute $u=X/r$, $v=Y/r$, $k=\kappa/r$.
Multiplication by $r$ gives

$$
\max(0,X+Y+Z-1)\le\kappa\le\min(X,Y).
$$

At $r=0$, the extra mode has all probability and $X=Y=\kappa=0$;
conditioning is unnecessary. The bounds thus apply to the entire
five-mode domain, including its apex.

For fair Bernoulli marginals, the laws
$\tfrac12(\delta_{00}+\delta_{11})$ and
$\tfrac12(\delta_{01}+\delta_{10})$ have the same marginal data.
An additive target has the same expectation under both, while the
distribution of that target need not agree. This is a classical coupling
input. Its realization by actual legal native FIB windows and its
continuing-reply consequences are supplied by
[the occupancy-pyramid volume](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md),
not by this probability paper. No theorem about a native FIB reader,
quantum instrument or acquired archive is attributed to the paper.
