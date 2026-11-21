---
bibkey: snellman2026kozlov
authors: Jan Snellman
year: 2026
title: "Hilbert functions over the exterior algebra and f-vectors in higher rank III: Lattice points of the Kozlov polytope"
doi: 10.48550/arXiv.2611.26110
url: https://arxiv.org/pdf/2611.26110v1#page=52
claim: "Section 10 item 2 asks whether the equal-shift Kozlov lattice count minus the proper sumset count is always divisible by r(r+1), extending the factor in Corollary 35."
strata_touched:
  - D5/S3/Combinatorics/Kozlov/ChainedCount
  - D5/S3/Combinatorics/Kozlov/ConvexHull
  - D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility
  - D5/S3/Combinatorics/Kozlov/LatticeCount
  - D5/S3/Combinatorics/Kozlov/LexFamilyShadow
  - D5/S3/Combinatorics/Kozlov/LexGreedySplit
  - D5/S3/Combinatorics/Kozlov/LexPositionShadow
  - D5/S3/Combinatorics/Kozlov/LexShadowSize
  - D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial
  - D5/S3/Combinatorics/Kozlov/ProperModel
  - D5/S3/Combinatorics/Kozlov/ProperSumset
  - D5/S3/Combinatorics/Kozlov/TransferCount
  - D5/S3/Combinatorics/Kozlov/TransferEndpoints
license: CC-BY-4.0
triage: anchor
---

# Equal-shift counts of the Kozlov polytope

## Verified locator

Part III, arXiv:2611.26110v1, §10 item 2, p. 52, asks whether the
divisibility in Corollary 35 holds for every positive ground-set size.
[Versioned PDF](https://arxiv.org/pdf/2611.26110v1#page=52) · [DOI 10.48550/arXiv.2611.26110](https://doi.org/10.48550/arXiv.2611.26110)

> At equal shifts, find the polynomial L_{Koz(n)}(r) − a(r) for general n: it vanishes for n ≤ 3, and at n = 4, 5 (Corollary 35) it is divisible by r(r + 1). Is it always?

For any positive ground-set size, the proper carrier consists of the
f-vectors of downsets containing the empty face and every singleton.
The rank-r sums allow repetition and are counted as distinct vectors.
The lattice count uses integer points inside the rank-r real dilate of
the convex hull of the same proper carrier. Both count polynomials are
specified at every positive natural rank. The divisibility question is
the final sentence of the excerpt. A general formula and the preceding
fill-rate questions are separate source requests.

## Related results

Part I, arXiv:2609.23605v1, establishes the rank-one polytope and its
normalized inequalities. Part II, arXiv:2610.14985v1, Theorems 36 and 41,
supplies the proper-sum polynomial and its transfer construction.
Part III, Proposition 31(2), supplies the Ehrhart root at minus one for
the stated range n ≥ 3. Corollary 35 gives the two small-size divisibility
cases identified in the question. The positivity and boundary
conventions used for the general statement also include n = 1.

## Lean source license

The adapted Lean code is from Jan Snellman's immutable
[exterior-convex tree](https://gitlab.liu.se/jansn19/exterior-convex/-/tree/2f05ce99d059c305ffcf6142fcf9efbbca02e24f).
That code is MIT-licensed. Each adapted module cites its original file
and carries the MIT copyright and permission notice. An equivalent
declaration in the project's pinned Mathlib is the criterion for
replacing a transplant with a direct import and use of that declaration.
