---
bibkey: gudder2019finiteconvexeffect
authors: Stan Gudder
year: 2019
title: "Finite-Dimensional Convex Effect Algebras"
doi: 10.48550/arXiv.1912.05110
url: https://arxiv.org/abs/1912.05110v1
claim: "For random variables f, g on a finite set X and probability measures on X, the pair {f, g} is informationally complete (IC) if equal distributions of f and of g force equal measures. Strongly complementary pairs are IC and IC pairs are complementary; a complementary pair need not be IC, and finding a simple characterization of IC pairs is stated as an open problem."
strata_touched:
  - D5/S3/Observer/Tomography/InformationallyCompletePairForest
license: citation-only
triage: anchor
---

# Gudder, Finite-Dimensional Convex Effect Algebras

S. Gudder, arXiv:1912.05110v1 [quant-ph] (11 December 2019). Quotations are from the v1 TeX source, with the source's macros `\pscript`, `\rscript` and `\brac` expanded.

Section 5 reduces sharp convex effect algebras to classical probability on $X=\{1,2,\ldots,n\}$: with $\mathcal P(X)$ the probability measures and $\mathcal R(X)$ the random variables $f\colon X\to\mathbb R$, the distribution of $f$ in $\mu$ is

> $$\Phi_{f,\mu}(\Delta)=\mu[f^{-1}(\Delta)]=\sum\{\mu_i\colon f(i)\in\Delta\}$$

for $\Delta\subseteq\mathbb R$, and

> A set of two random variables $\{f,g\}$ is IC if $\Phi_{f,\mu}=\Phi_{f,\nu}$ and $\Phi_{g,\mu}=\Phi_{g,\nu}$ imply that $\mu=\nu$.

The partition $P(f)$ of $X$ into level sets defines complementary pairs (every nonempty intersection of blocks of $P(f)$ and $P(g)$ is a singleton) and strongly complementary pairs. Theorem 5.2 proves that strongly complementary pairs are IC and that IC pairs are complementary; Example 5 gives a complementary pair, with $P(f)=\{\{1,2\},\{3,4\}\}$ and $P(g)=\{\{1,3\},\{2,4\}\}$, that is not IC. The section ends:

> We conclude from Example 5 that complementarity is a necessary but not a sufficient condition for IC. It is an open problem to find a simple characterization of IC for a pair $\{f,g\}\subseteq\mathcal R(X)$.

## Verified locator

Source: https://arxiv.org/abs/1912.05110v1
- DOI: https://doi.org/10.48550/arXiv.1912.05110 (arXiv-issued DataCite DOI; the arXiv record lists only version 1 and no journal reference).
- URL: https://arxiv.org/abs/1912.05110v1. The e-print is the single file `finitedimensionalCEA.tex` (765 lines, md5 `9dfe03bd484881c9db3b8b737095b005`). Locations:
  - distributions and IC random variables, l. 435–439; IC pairs, l. 474;
  - complementary pairs, l. 507–508; Theorem 5.2, l. 535–559;
  - Example 5, l. 563–586; the open problem, l. 588.
