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
