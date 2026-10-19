---
slug: nikiforov-2015-ky-fan-asymptotic-gap
bibkey: nikiforov2015extrema
doi: null
url: https://arxiv.org/abs/1502.00359v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/KyFanGap/Defs.conjecture
---

# Nikiforov: asymptotic graph Ky Fan gaps

## Problem

The source is V. Nikiforov, *Extrema of graph eigenvalues*,
arXiv:1502.00359v1, §4, Conjecture 4.7. Its definition is:

> ξk (n) = max λ∗1 (G) + · · · + λ∗k (G)

The maximum is over graphs of order n. Starred eigenvalues denote
singular values, equivalently the absolute eigenvalues of the real
symmetric adjacency matrix, in decreasing order. The text preceding
the conjecture states:

> Theorem 4.3 does not shed any light on the case when k is not an exact square, so we suggest the following concrete conjecture.

Conjecture 4.7 states:

> There exist infinitely many integers k such that lim_{n→∞} ξk (n)/n < (1+√k)/2.

The repeated statement is Conjecture 3.20 of *Beyond graph energy: norms
of graphs and matrices*, arXiv:1510.02850v2, §3.3.

## Motivation

The stronger target is a positive gap for every nonsquare positive k,
uniformly over every order n≥k and every symmetric zero-one matrix,
including matrices with nonzero diagonal. The uniform gap and existence
of the normalized graph-maxima limit settle the graph question.
There are infinitely many positive nonsquares.

## Gap

Finite-order failure of equality does not exclude a sequence of orders
whose normalized Ky Fan sums approach the universal upper bound.
The proof turns a near-extremal Ky Fan value into both
a bounded rank-coordinate approximation of a sign matrix and concentration
of that same matrix's row sums at 1/sqrt(k).

## Route

Center A by B=2A-J, normalize T=B/n, and choose a signed orthonormal
family attaining the Ky Fan sum. Near equality in the Frobenius and
constant-vector bounds controls approximation and row-sum
errors. Smooth the family by x(r,i)=sqrt(n)(T u_i)(r)/c, with
c=1/sqrt(k). Cauchy-Schwarz bounds every coordinate by sqrt(k), and the
bilinear kernel H satisfies H/n=TQT/c. The identity Q^3=Q controls
the kernel approximation error by the Frobenius error T-cQ.
Fourth-moment compression reduces the coordinate family to
choose(k+4,4)+1 weighted nodes, preserving the sign and row-sum defects.
Compactness gives a joint zero-defect limit. Restriction to its positive
weight support gives a symmetric rational sign matrix with constant
weighted row sum 1/sqrt(k), contradicting irrationality for nonsquare k.

## Falsifier

For a fixed positive nonsquare k, a sequence of symmetric zero-one matrices
of orders at least k whose normalized Ky Fan sums tend to (1+sqrt(k))/2
would refute the uniform-gap statement. Failure of an intermediate
approximation estimate alone would invalidate that route without refuting
the original infinitude conjecture. Finiteness of the set of prefixes
admitting a strict limiting gap would refute the original conjecture.

## Evidence

The pinned definitions are in
[Defs.lean](../D5/S3/Combinatorics/Graph/KyFanGap/Defs.lean).
The exact settlement is `D5.S3.Combinatorics.Graph.KyFanGap.result` in
[Result.lean](../D5/S3/Combinatorics/Graph/KyFanGap/Result.lean).
The live intermediate results are `uniform_gap` in NearExtremal,
`bilinear_defect_gap` in UniformGap, `exists_model_defect_gap` in Compactness,
and `tendsto_xi_div` in BlowUp. The latter identifies the limit explicitly
as the supremum over orders m+k. The uniform theorem applies to every
positive nonsquare k, while the final infinitude argument uses primes.


The source equation (12) and Theorem 4.3 give the universal upper bound
and finite-order equality restriction. Nikiforov arXiv:1007.3949 and
arXiv:1510.02850v2, Theorem 3.16, also concern finite-order equality.
Sivashankar–Tang–Wakhare, arXiv:2608.02429v1, §6.2, Proposition 6.1,
settles Conjecture 4.2 for τk, the sum of the largest eigenvalues by
algebraic order. The negative eigenvalues contribute differently to ξk,
so that proposition does not settle this target. The available source
extracts do not establish an exhaustive citation-index check.

## Triage

- PROVED: the signed Ky Fan upper and attainment formulas for real symmetric matrices.
- PROVED: the universal zero-one upper bound and the positive uniform gap for every positive nonsquare k and every order n≥k.
- PROVED: blow-up lower bounds, monotonicity under isolated-vertex padding, and convergence of xi(k,n)/n to sup_m xi(k,m+k)/(m+k) for every k≥1.
- PROVED: the pinned conjecture holds, using infinitely many primes as positive nonsquare prefixes.
- OPEN: an effective or optimal value of the positive gap.
- ASSUMED-UNVERIFIED: exhaustive citation-index coverage beyond the supplied source readings.


## ASSUMED-UNVERIFIED

The quoted source extracts and the literature reading above are supplied
source information. The original papers and citation indexes have not been
independently rechecked under the offline constraint. The stated reading
scope distinguishes the finite-order equality results and the tau_k
settlement from the xi_k asymptotic question; it does not certify an
exhaustive priority claim. The [Library note](../Library/Eigenstructure/nikiforov2015extrema.md)
records the source locators and the mathematical distinction.
