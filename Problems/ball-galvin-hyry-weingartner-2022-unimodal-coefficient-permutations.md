---
slug: ball-galvin-hyry-weingartner-2022-unimodal-coefficient-permutations
bibkey: ball2022independent
doi: 10.1002/jgt.22724
url: https://doi.org/10.1002/jgt.22724
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/RealRootedPermutations/Defs.claim
---

# Ball–Galvin–Hyry–Weingartner: unimodal coefficient permutations

## Problem

T. Ball, D. Galvin, C. Hyry, and K. Weingartner, *Independent set and
matching permutations*, Journal of Graph Theory 99(1) (2022), 40–57,
Section 4, Question 4.6 (arXiv:1901.06579v2), asks:

> Which unimodal permutations of [n] can arise via (1) from the coefficient sequence of a polynomial of the form (1+r₁x)(1+r₂x)⋯(1+rₙx) with rᵢ real and nonnegative?

Equation (1) means $a_{\pi(1)}\le\cdots\le a_{\pi(n)}$, excluding the
constant coefficient. Equation (4) means that the inverse positions
increase up to the final value $m=\pi(n)$ and decrease afterwards.

The formal reading takes the polynomial to have degree $n\ge1$, so
all $r_i>0$. If zero parameters are allowed without the degree
condition, trailing coefficients vanish; choosing every $r_i=0$
makes all nonconstant coefficients zero and every permutation arises
trivially. The full-degree reading agrees with the source's restriction
to unimodal permutations.

## Motivation

The question relaxes the matching-permutation problem for unweighted
simple graphs, stated as Problem 1.6 and attributed to
Alavi–Malde–Schwenk–Erdős Problem 2. The source shows that a vanishing
proportion of unimodal permutations are matching permutations of such
graphs. Positive polynomial factors permit arbitrary positive edge
weights on disjoint edges. The source exhibits the decreasing
permutation; the polynomial answer is that all $2^{n-1}$ unimodal
permutations arise, even with strict coefficient comparisons.

## Gap

Coefficient unimodality alone does not control every weak sorting in
the presence of ties. Strict log-concavity restricts ties to the peak
and forces every weak sorting permutation to satisfy (4). Conversely,
a coefficient sequence with a desired order must come from one common
positive factor family; assigning its coefficients independently does
not establish real-rootedness. Integer exponent heights supply that
family and separate its coefficient scales.

## Route

Use one-based coefficient indices $k=1,\ldots,n$ and inverse positions
$\rho(k)=\pi^{-1}(k)$. Set

$$
H_0=0,\qquad H_k=2^n-2^{n-\rho(k)},\qquad
b_i=H_i-H_{i-1},\qquad T=2^n+1,\qquad r_i=T^{b_i}.
$$

Unimodality makes the integer increments
$b_1>\cdots>b_n$ strictly decreasing. Before the peak the preceding
power of two is at least twice the current one; after the peak the
following power has that property. The first increment satisfies the
same strict comparison using the bound $2^{n-1}$ on the first weight.

The coefficient $a_k$ is the sum of $\prod_{i\in S}r_i$ over
$k$-element subsets $S$. Decreasing increments make the prefix
$\{1,\ldots,k\}$ maximize $\sum_{i\in S}b_i$, with value $H_k$.
All terms are positive and there are at most $2^n$ terms, so

$$
T^{H_k}\le a_k\le2^n T^{H_k}.
$$

The distinct integer heights increase with inverse rank. Since
$T>2^n$, the upper bound at one height is strictly below the lower
bound at the next height. Thus the coefficient order equals the height
order. Factor induction on the coefficient recurrence
$c_k\mapsto c_k+r c_{k-1}$ proves positivity and strict interior
log-concavity for every positive factor family. The resulting persistent
decrease property proves the converse, including a tie at the peak.

## Falsifier

A positive factor family with a nonunimodal weak sorting would refute
necessity. A unimodal permutation for which no positive factor family
has the specified weak order would refute sufficiency. A failure of
strictly decreasing increments or the subset coefficient bounds would
invalidate the construction without refuting the existence statement.

## Evidence

[Defs.lean](../D5/S3/Combinatorics/RealRootedPermutations/Defs.lean)
fixes the coefficient product, weak sorting and inverse-position
definition. It uses `Fin(n+1)` to cover every positive size.
[LogConcave.lean](../D5/S3/Combinatorics/RealRootedPermutations/LogConcave.lean)
proves positivity and strict log-concavity internally and exports
`unimodal_of_arises`.
[Realization.lean](../D5/S3/Combinatorics/RealRootedPermutations/Realization.lean)
proves the subset bounds and exports `realize_strict`.
[Result.lean](../D5/S3/Combinatorics/RealRootedPermutations/Result.lean)
proves `result : claim`, the equivalence for every positive size.
The axiom closure is restricted to `propext`, `Classical.choice`, and
`Quot.sound`.

The realization construction was derived with the assistance of the ChatGPT Pro model.

## Triage

- PROVED (formalized): a permutation of $[n]$ weakly sorts $a_1,\ldots,a_n$ for some $\prod_i(1+r_i x)$ with every $r_i>0$ if and only if it is unimodal. Every unimodal permutation has a strict realization by the exponent-height construction above. The coefficient sequence of every such positive product is positive on its support and strictly log-concave at every interior index.
- PROVED (formalized mechanism): the largest subset term is $T^{H_k}$, attained by the prefix because the exponent increments strictly decrease. At most $2^n$ subset terms contribute. The bounds $T^{H_k}\le a_k\le2^nT^{H_k}$ identify the coefficient order with the height order.
- PROVED (consequences of the formalized construction): the chosen parameters are positive rationals, since they are integer powers of the positive integer $T$. Strictly decreasing exponents and $T>1$ make them pairwise distinct. These properties are visible in the constructed witness and slope inequalities; the exported existential theorem states positivity and strict sorting, without separate rationality or distinctness conjuncts. The same factors enumerate weighted matchings of $n$ disjoint edges with edge weights $r_i$, giving the weighted interpretation of the graph question; this graph interpretation is not encoded in the Lean development.
- COMPUTED (exact rational arithmetic, outside the Lean development): the construction verified for all 511 unimodal permutations with $1\le n\le9$; 3,000 random positive rational root vectors with $n\le8$ produced only unimodal weak sortings. These are numerical checks and not part of the formal proof.
- OPEN: which unimodal permutations are matching permutations of unweighted simple graphs; the source shows a vanishing proportion. Minimal bit size or magnitude of realizing positive rational roots is also open here.

## ASSUMED-UNVERIFIED

The source quotations and bibliographic locators are attributed to the
article and its author manuscript. The finite experiment counts are
external to the Lean evidence. No claim of minimal root size or
unweighted graph realization follows from the polynomial equivalence.

Searches covered web queries for the exact question with matching permutations, real-rooted and unimodal permutations; arXiv title and author combinations; this repository's D5, Problems and Library for the DOI, arXiv identifier and matching or unimodal permutations; repository pull requests and discussions; Formal Conjectures and GitHub code. The source article was located. Later work on independent set sequences of trees, including arXiv:2510.18826, does not answer this polynomial question.

No answer to the question was found in that scope. Citation indexes were not exhaustively checked; this is not a priority certification.

The [library note](../Library/PermutationPatterns/ball2022independent.md)
records the source definitions, locators and full-degree boundary.
