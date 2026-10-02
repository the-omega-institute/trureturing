---
bibkey: shirokov2026moreauyosidaeof
authors: M. E. Shirokov
year: 2026
title: "The Moreau-Yosida approximation of the EoF: basic properties and accuracy estimates"
doi: null
url: https://arxiv.org/abs/2609.30246v1
claim: "we may conjecture, at the moment, that the function E_F^lambda does not increase under selective LOCC-operations"
strata_touched:
  - D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation
license: citation-only
triage: anchor
---

# The Moreau-Yosida approximation of the EoF

M. E. Shirokov, arXiv:2609.30246v1, Section 7, p. 20.

## Verified locator

https://arxiv.org/abs/2609.30246v1

## Statement

The finite-dimensional entanglement of formation is defined in (EF-d), equation (1), p. 2, by

$$
E_F(\rho)=\inf_{\sum_k p_k\varrho_k=\rho}\sum_k p_k S([\varrho_k]_A).
$$

> where the infimum is taken over all finite ensembles $\{p_k,\varrho_k\}$ of pure states in $\mathfrak S(\mathcal H_{AB})$ having $\rho$ as their average state

The entropy uses the natural logarithm. Equation (EFA), equation (13), p. 6, defines, for $\lambda>0$,

$$
E_F^\lambda(\rho)=\inf_{\sigma\in\mathfrak S(\mathcal H_{AB})}
\left\{E_F(\sigma)+\frac{1}{2\lambda}\|\rho-\sigma\|_1\right\}.
$$

The source footnote on p. 7 specifies:

> It is essential that we use $\|\rho-\sigma\|_1$ instead of $\|\rho-\sigma\|^2_1$

Section 7 asks:

> Open question: can the function $E^{\lambda}_F$ increase under selective LOCC-operations?

The conjectural sentence is:

> It is proved in Section 3 (Corollary 1) that the function $E^{\lambda}_F$ does not increase under nonselective LOCC-operations for every $\lambda>0$. Unfortunately, the (quite simple) arguments used to prove this property are not generalized to selective LOCC-operations. At the same time, all the attempts of ChatGPT-5.6 to find a counterexample were unsuccessful. So, *we may conjecture, at the moment, that the function $E^{\lambda}_F$ does not increase under selective LOCC-operations* as well.

The formal claim uses the standard selective inequality: the probability-weighted
sum of the normalized branch values is at most the input value. It quantifies over
finite dimensions and finite-round local Kraus instruments, with several Kraus
operators allowed per classical outcome and the full classical outcome history
retained. The one-round two-outcome Alice projective measurement is a member of
this class, and also a member of the larger LOCC classes used in the source.

The formal refutation gives an input on $\mathbb C^5\otimes\mathbb C^3$ and
$\lambda=7/2$ with input value at most $1/7$ and output average at least $3/20$.
It uses the full finite pure-state convex roof and the unsquared trace norm.
The pure-state cost is literally the von Neumann entropy of Alice's reduced
density state, with the frozen rank-one density-state constructor and partial
trace. Both formation functions take values in $[0,+\infty]$ via
`ENNReal.ofReal` of their nonnegative real expressions for $\lambda>0$.
