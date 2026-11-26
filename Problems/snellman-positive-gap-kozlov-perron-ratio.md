---
slug: snellman-positive-gap-kozlov-perron-ratio
bibkey: snellman2026kozlov
doi: 10.48550/arXiv.2611.26110
url: https://arxiv.org/pdf/2611.26110v1#page=52
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.positive_gap_perron_root_ratio
---

# Snellman's positive-gap Kozlov Perron-root ratio

## Problem

Jan Snellman asks to “prove that the Perron-root ratio of Observation 22 is below 1 for n ≥ 4 and every gap δ ≥ 1.” [Part III, §10 item 2](https://arxiv.org/html/2611.26110v1#S10.I1.i2.p1)

Let $S_n$ be the distinct f-vectors of downsets on $n$ vertices containing the empty face and all singletons. Let $L_n$ be the integer points of the real convex hull of $S_n$. For either carrier, the row $a$, column $b$ entry counts incoming vectors of top degree $b$ whose first deficiency plus the gap exceeds $a$. The proper transfer of Part II includes predecessor and incoming top degrees $-1,0,1,\ldots,n$. The lattice transfer of Part III uses degrees $1,\ldots,n$. The ratio is the complex spectral radius of the full proper transfer divided by that of the lattice transfer, after entrywise casting the counts to complex numbers. [Part II, Theorem 41](https://arxiv.org/pdf/2610.14985v1#page=31) · [Part III, Corollary 33 and equation (42)](https://arxiv.org/pdf/2611.26110v1#page=29)

## Motivation

The ratios measure the relative exponential growth rates of the two constant-gap transfer products. Observation 22 reports the strict ratio and a separate rank-two behavior from computations for $n\le 7$. [Observation 22](https://arxiv.org/html/2611.26110v1#Thmdefinition22)

## Gap

The source gives the transfer product formulas. Part II, Lemma 44, gives the proper support and the two zero columns. Part III, Proposition 2, identifies the literal hull by normalized binomial inequalities. The source asks for the strict ratio at every admissible ground-set size and gap. [Part II, Lemma 44](https://arxiv.org/pdf/2610.14985v1#page=32) · [Part III, Proposition 2](https://arxiv.org/pdf/2611.26110v1#page=8) · [Preregistration #33426](https://github.com/the-omega-institute/trureturing/issues/33426)

## Route

The vector $(1,n,2,1,0,\ldots,0)$ satisfies the normalized binomial chain for $n\ge4$, so it belongs to the lattice carrier. A triple in any proper downset forces its three pairs, so this vector lies outside the proper carrier. Its top degree is three and its first deficiency is two. It gives a strict lattice advantage at $(1,3)$ at every positive gap.

Complete skeletons give all consecutive transitions and loops in both positive-degree supports. The full proper transfer has block form $\bigl(\begin{smallmatrix}0&C\\0&A\end{smallmatrix}\bigr)$ with the proper positive-degree block $A$. Its characteristic polynomial is $X^2\operatorname{charpoly}(A)$, so the full matrix and that block have the same spectral radius.

For the lattice matrix $B$, choose a positive left Perron vector $u$, and for the proper block $A$ choose a positive right Perron vector $v$. Every term of $u^\top(B-A)v$ is nonnegative, and the term at $(1,3)$ is positive. This equals $(\rho(B)-\rho(A))u^\top v$. Both Perron roots are positive and finite, so their order gives the strict ratio in the published direction.

## Falsifier

A natural $n\ge4$ and a natural $\delta\ge1$ for which either of the two literal complex spectral radii is zero or their proper-to-lattice ratio is at least one would contradict the statement.

## Evidence

The settling result is `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.positive_gap_perron_root_ratio`. Its hypotheses are $4\le n$ and $1\le\delta$. It gives positivity of both complex spectral radii, their strict order, and the strict ratio with positive real denominator. The proof uses the frozen Kozlov carriers and the Perron theorem for weighted networks.

## Triage

Tier 1, theorem, resolution Proved. The admission basis is `open-problem-resolution` for the ratio clause of §10 item 2. The computational utility is `none` for this symbolic proof.

### What the settlement shows

The positive-gap ratio is proved by `D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.positive_gap_perron_root_ratio`. A single lattice vector of degree three distinguishes the two transfers at every size and gap in scope. The comparison is pointwise in $n$ and $\delta$. A uniform bound separated from one, the rank-one limit and rate, and the separate rank-two nonmonotonicity question are open here.

## ASSUMED-UNVERIFIED

Global priority remains unverified. The bounded source qualification covered Parts I–III, the author's immutable source archive, and the related Lean and citation searches described in the preregistration.
