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
normalized inequalities. Part III, Proposition 2 and equation (14), gives
the ratios and the barycentric weights of the dilate. Theorem 6 and
Corollary 7 give the integral chained decomposition, and Corollary 33
gives the lattice transfer formula.
[Part III, Proposition 2](https://arxiv.org/pdf/2611.26110v1#page=8) ·
[Theorem 6 and Corollary 7](https://arxiv.org/pdf/2611.26110v1#page=11) ·
[Corollary 33](https://arxiv.org/pdf/2611.26110v1#page=29)

Part III, Corollary 34, states that both equal-shift counts are
polynomials. It credits Part II, Theorem 36, for the proper count and
uses Part II, Theorem 41, for its transfer formula. Part II, Lemma 40
and Theorem 41, give the proper lex representative used to obtain the
proper transfer formula.
[Part III, Corollary 34](https://arxiv.org/pdf/2611.26110v1#page=30) ·
[Part II, Theorem 36](https://arxiv.org/pdf/2610.14985v1#page=27) ·
[Lemma 40](https://arxiv.org/pdf/2610.14985v1#page=30) ·
[Theorem 41](https://arxiv.org/pdf/2610.14985v1#page=31)

Part III, Proposition 31(2), supplies the Ehrhart root at minus one for
the stated range n ≥ 3. Corollary 35 gives the two small-size divisibility
cases identified in the question. The general divisibility statement
includes n = 1.
[Part III, Proposition 31](https://arxiv.org/pdf/2611.26110v1#page=28) ·
[Corollary 35](https://arxiv.org/pdf/2611.26110v1#page=30)

## Lean source license

The adapted Lean code is from Jan Snellman's immutable
[exterior-convex tree](https://gitlab.liu.se/jansn19/exterior-convex/-/tree/2f05ce99d059c305ffcf6142fcf9efbbca02e24f).
That code is MIT-licensed. Each adapted module cites its original file
and carries the MIT copyright and permission notice. An equivalent
declaration in the project's pinned Mathlib is the criterion for
replacing a transplant with a direct import and use of that declaration.

- The normalized hull uses the skeleton and ratio declarations in
  `Spine/LYM.lean`, the literal hull equality in `Spine/KozlovThm.lean`,
  and the real realization of the natural carrier in `Counting/Duality.lean`.
  [Skeletons and the chain](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Spine/LYM.lean#L76)
  · [Ratios and telescope](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Spine/LYM.lean#L164)
  · [Hull](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Spine/KozlovThm.lean#L145)
  · [Real realization](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Counting/Duality.lean#L322)
- The literal proper model uses the face and degree-count conventions
  of `Spine/Complexes.lean`, the proper carrier of `Counting/Duality.lean`,
  and the chaining relation and degree statistics of `Counting/Chaining.lean`
  and `Counting/Stats.lean`.
  [Proper families](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Spine/Complexes.lean#L44)
  · [Proper carrier](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Counting/Duality.lean#L309)
  · [Chaining](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Counting/Chaining.lean#L361)
  · [Top](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Counting/Stats.lean#L105)
  · [First deficiency](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Counting/Stats.lean#L112)
- The shadow comparisons and greedy splitting use `ModuleKK/GreedyPQ.lean`,
  `ModuleKK/Greedy.lean`, `ModuleKK/LexShadow.lean`, and `ModuleKK/LexF.lean`.
  [Shadow inequalities](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/ModuleKK/GreedyPQ.lean#L124)
  · [Greedy split](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/ModuleKK/Greedy.lean#L113)
  · [Lex shadows](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/ModuleKK/LexShadow.lean#L259)
  · [Position-first lex shadows](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/ModuleKK/LexF.lean#L458)
- The transfer recurrence, finite matrix expansion and literal lattice
  carrier are given in `Lattice/TransferEhrhart.lean`. The local entry
  polynomial uses the same binomial expansion in the power variable.
  [Transfer recurrence](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Lattice/TransferEhrhart.lean#L355)
  · [Matrix expansion](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Lattice/TransferEhrhart.lean#L150)
  · [Polynomial evaluation](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Lattice/TransferEhrhart.lean#L278)
  · [Lattice carrier](https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Lattice/TransferEhrhart.lean#L595)
