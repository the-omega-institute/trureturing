---
bibkey: doughertyblissgalvanpolleyshuster2026enumerating
authors: Robert Dougherty-Bliss, Alejandro B. Galvan, Michaela Polley, and David Shuster
year: 2026
title: "Enumerating separable derangements"
doi: null
url: https://arxiv.org/abs/2608.27583v1
claim: "The paper gives an algorithm and asymptotic bounds for separable derangements, while Conjecture 15 leaves the limiting derangement proportion open."
strata_touched: []
license: citation-only
triage: anchor
---

# Enumerating separable derangements

Dougherty-Bliss, Galvan, Polley, and Shuster give a polynomial-time algorithm
for the number `b_n` of separable derangements (Theorems 1 and 10). Theorems
12 and 13 give bounds for `b_n / s_n` and identify the exponential growth
constant `3 + 2 * sqrt(2)`, where `s_n` counts separable permutations. These
results partially answer Vatter's Problem 4.4 and provide bounds relevant to
Question 4.5.

The paper's Conjecture 15 states that `b_n / s_n` tends to zero. Thus the
limiting ratio remains a conjecture in this source, and numerical monotonicity
or fitted asymptotics do not settle it. This note makes no claim about the
separate largest-limit question following Vatter's Question 4.3 and has no
full formal D5 settlement attached to it. The source is released under CC BY 4.0;
this repository note records citation and status only.

## Related asymptotic inputs and resolution boundary

Equation (7) gives the actual separable-count asymptotic with exponential
constant `3 + 2 * sqrt(2)` and power `n^(-3/2)`. This is a known input for
fixed-shift count ratios, rather than a new settlement of Conjecture 15.
Pinsky's [The Infinite Limit of Separable Permutations](https://arxiv.org/html/1911.05565v2)
provides finite decomposition and scalar length limits. Transporting finite
histories to an infinite law still requires the actual coupled transitions
and absolute position/value labels.

The [Brownian limit of separable permutations](https://arxiv.org/html/1602.04960v3),
Theorem 1.6, concerns normalized permuton convergence; an absolute
fixed-point probability needs an additional argument. The recursive and
Brownian separable permuton models are distinct, as shown by Féray and
Rivera-López in their [recursive separable permuton limit result](https://arxiv.org/html/2306.04278v2),
Proposition 1.3. A recursive sampler cannot replace the actual uniform class.

The official arXiv record remains v1. A bounded check of arXiv metadata and
the related primary sources above identified no complete resolution of the
full actual-class, all-length limit. Forward-citation coverage is incomplete;
this is not a global originality certificate. The finite bridge in
`D5/S1/Words/Patterns/Separable/StableEndpointCodes.lean` supplies bounded codes
independent of the initial length, complete successful-history fibers, and
exact fixed-family mass and absolute-coordinate cylinder sums under
`n > H*K + max(2*K, max(m,B))`. Cap fibers retain their selected-leaf counts,
including the threshold-satisfying four-of-twenty-two example. These finite
statements do not settle the conjecture: actual count-ratio and sign-half
interfaces, the infinite coupled law, truncation tails, occupation and hitting
transfer remain needed.

## Verified locator

- arXiv: https://arxiv.org/abs/2608.27583v1
- HTML: https://arxiv.org/html/2608.27583v1, Theorems 1, 10, 12, 13 and Conjecture 15
- Submitted August 27, 2026 (version v1)

## Actual occupation comparison

For positive length, let `M_n(e)` count actual sum-indecomposable avoiders
with at least one point on displacement diagonal `e`, once per permutation.
With `b=sqrt(2)-1`, `rho=b^2` and `a=1-b`, the raw mass is
`C(e)=sum_(n>=1)rho^n M_n(e)`, while `O(e)=(2/a)C(e)` is its normalized
version. The source diagonal counts are at-least-one events, rather than
expected numbers of points.

`OccupiedComparison.actual_occupation_subsolution_comparison` proves
summability of the actual shape weights, their total `b`, critical kernel
mass `1/2`, convergence of every occupied-count series, and the raw mass box
`0<=C(e)<=a/2` without additional premises. The native Schroder recurrence,
a uniform bound on nonnegative partial sums, and the Cauchy product supply
the critical analytic facts; the singleton correction is retained.

The theorem also supplies the two actual finite occupied-count recurrences
through the minimum-cut equivalence. The direct recurrence counts
left-hit/right-no-hit and right-hit, and the skew recurrence adds disjoint
factor events shifted by the opposite block lengths. These count each shape
once, including all natural lengths and integer displacements. Splitting the
actual hit fiber by the proper-cut predicate gives the full/indecomposable/
decomposable count partition. The native opposite-sign law identifies the
decomposable hit counts with opposite-orientation indecomposable hit counts
at lengths at least two. The actual singleton hit count is one on diagonal
zero and zero elsewhere in either orientation.

Inversion preserves the avoidance pair and both proper-cut classes and
negates every hit displacement, giving reflection of actual occupied
counts. The absolutely convergent joint sums transport the finite
recurrences with their actual shifts and intersection correction. Writing
T for full occupied mass, P for direct-decomposable occupied mass and
V(x)=x squared/(h+x), the direct recurrence gives T=2C-2V(C) and
P=C-2V(C). Substitution in the skew recurrence and averaging its reflected
version establishes the literal nonlinear occupation equation, including
the forcing and singleton correction. Global comparison therefore has no
actual fixed-point premise.

The required positive logarithmic subsolution is not constructed. The
uniform all-integer lower bound registered in
[issue 15063](https://github.com/the-omega-institute/trureturing/issues/15063)
and the source Conjecture 15 remain unproved by this result.
