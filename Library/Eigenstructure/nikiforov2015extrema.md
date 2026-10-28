---
bibkey: nikiforov2015extrema
authors: Vladimir Nikiforov
year: 2015
title: "Extrema of graph eigenvalues"
doi: null
url: https://arxiv.org/abs/1502.00359v1
claim: "Conjecture 4.7 asks for infinitely many strict asymptotic gaps in graph Ky Fan singular-value sums."
strata_touched:
  - D5/S3/Combinatorics/Graph/KyFanGap/Defs
  - D5/S3/Combinatorics/Graph/KyFanGap/Compactness
  - D5/S3/Combinatorics/Graph/KyFanGap/UniformGap
  - D5/S3/Combinatorics/Graph/KyFanGap/NearExtremal
  - D5/S3/Combinatorics/Graph/KyFanGap/Result
license: citation-only
triage: anchor
---

# Graph Ky Fan asymptotic gaps

## Locator

https://arxiv.org/abs/1502.00359v1

V. Nikiforov, *Extrema of graph eigenvalues*, Linear Algebra and its
Applications 482, 158–190, arXiv:1502.00359v1, §4, equation (12),
Theorem 4.3 and Conjecture 4.7.

The definition in §4 is:

> ξk (n) = max λ∗1 (G) + · · · + λ∗k (G)

Here the maximum ranges over graphs of order n, and the starred values
are singular values in decreasing order. Following the finite-order
equality theorem, the text states:

> Theorem 4.3 does not shed any light on the case when k is not an exact square, so we suggest the following concrete conjecture.

Conjecture 4.7 states:

> There exist infinitely many integers k such that lim_{n→∞} ξk (n)/n < (1+√k)/2.

The same question is Conjecture 3.20 of *Beyond graph energy: norms of
graphs and matrices*, arXiv:1510.02850v2, §3.3, Linear Algebra and its
Applications 506, 82–138.

## Scope

The universal bound is ξk(n) ≤ (1+sqrt(k))n/2. Theorem 4.3 excludes
finite-order equality for nonsquare k. A strict bound separately at each
order does not imply a gap independent of the order.

The repository uniform-gap proof compresses coordinate moments through
degree four to a fixed number of weighted nodes. The limiting sign and
row-sum constraints must involve the same weights and the same symmetric
matrix. For a symmetric rational matrix, a nonzero constant weighted row
sum with weights of total mass one is rational. Thus the limiting
row sum 1/sqrt(k) is impossible when k is not a square. The source
paper supplies the conjecture and finite-order comparison; the uniform
compression argument and its formal proof are repository results.
Blow-ups and isolated-vertex padding establish the normalized graph
maximum limit, so the uniform theorem proves the conjectured infinitude.

## Related results

Sivashankar–Tang–Wakhare, *Graph Eigenvalues and Projection Constants*,
arXiv:2608.02429v1, §6.2, Proposition 6.1, concerns Nikiforov's
Conjecture 4.2 and the sum τk of the largest eigenvalues by algebraic
order. The present ξk includes large negative eigenvalues through their
absolute values. That proposition does not settle the ξk question.
Nikiforov arXiv:1007.3949 and arXiv:1510.02850v2, Theorem 3.16, concern
finite-order equality and do not supply the required uniform asymptotic
gap. These locators and quoted source extracts are the available reading;
an independent exhaustive citation-index check is not available.
