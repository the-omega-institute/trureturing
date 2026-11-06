---
slug: oeis-a394697-toroidal-king-peak-entropy
bibkey: kotesovec2026a394697
doi: null
url: https://oeis.org/A394697
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Pressure/ToroidalKingsPeakEntropy
---

# Toroidal king peak entropy

## Problem

For n at least three, use vertex set {0,...,n-1}² and join distinct
vertices when both cyclic coordinate distances are at most one.
Let c(n,k) count independent subsets of cardinality k and let
a(n)=max(0≤k≤n²)c(n,k). The A394697 conjecture asks whether
a(n)^(1/n²) tends to the literal A247413 constant through all integers.
A247413 is identified with the limit of A063443(m)^(1/m²), where
A063443 counts square tilings by unit and two-by-two squares.

## Qualification

This is a tier-one separately stated external conjecture. The exact
event and source qualification are preregistered in
[issue 27011](https://github.com/the-omega-institute/trureturing/issues/27011).
The qualified sources include Calkin, James and Purvis, Liang's
arXiv:2505.12776v2 and arXiv:2507.04007v2, Hildebrant's
arXiv:2604.14416v1, and Friedland and Peled's arXiv:math/0402009v1.
Their free-board entropy, maximum-versus-total mechanism, cylindrical
comparisons and periodic limsup results receive their existing credit.
The bounded source check does not establish worldwide openness or
priority. No matching Lean result was identified in the inspected
repository, pinned Mathlib, Loogle and bounded GitHub code searches.

## Mathematical route

Write F(n) for the free square count and T(n) for the toroidal total.
Leaving the last row and column empty gives F(n-1)≤T(n). Forgetting
periodic edges gives T(n)≤F(n). Partitioning configurations by
cardinality gives T(n)≤(n²+1)a(n), and each coefficient is at most T(n).
Thus F(n-1)/(n²+1)≤a(n)≤F(n), without a parity restriction.

For free rectangles, restricting at a straight cut is injective into
the product of the two smaller configuration families. After taking
logarithms, this gives subadditivity in one side. Transposition gives
symmetry, and the binary vertex-subset bound is linear in area.
Pinned Mathlib's one-dimensional Fekete theorem yields each
fixed-width entropy. Their normalized infimum is the square entropy:
a width-k cut bounds the normalized diagonal above by the width-k
entropy plus a term at most k log(2)/n. The corresponding Fekete
infimum bound supplies the lower bound.

A tiling is encoded by the lower-left positions of its two-by-two
tiles. They must be pairwise disjoint; all remaining cells receive
their uniquely determined unit tiles. Two such tiles overlap exactly
when both anchor-coordinate gaps are at most one. Consequently the
tiling count at m equals F(m-1). This is the source's exact index shift.

The shifted free logarithmic limit and
log(n²+1)/n²→0 squeeze log(a(n))/n² to the same entropy. Exponentiation
identifies its root limit with the independently defined tiling limit.

## Formal statement and boundary

`ToroidalKingsEmptySeam` defines the actual bounded vertex sets,
adjacencies, all independent subsets, every cardinality coefficient,
the maximum, rectangular counts and tiling placements.
`RectangularCountEntropy.square_log_limit` proves the required square
limit from the rectangular inequalities, rather than assuming it.
`ToroidalKingsPeakEntropy.a247413` is defined from the tiling sequence
independently of toroidal counts. Its `result` states that for every
positive real epsilon there is N≥3 such that every integer n≥N has
absolute root error less than epsilon. No even-only or total-count
replacement occurs.

The formal tiling object is the disjoint-large-tile placement encoding
with canonical unit completion. A separate partition-type tiling object
and a bijection theorem for `tilingBlocks` are not provided;
`tilingBlocks` is not on the limit theorem's dependency path.


## Triage

- **Kernel-checked:** `ToroidalKingsPeakEntropy.result` proves the full
  maximum-coefficient limit through every integer $n\ge3$, including
  odd side lengths, with the independently defined A247413 constant.
- **Kernel-checked:** `RectangularCountEntropy.square_log_limit` gives
  square-area convergence from rectangular subadditivity, symmetry
  and area bounds. `ToroidalKingsEmptySeam.free_log_limit` applies it
  to free king configurations.
- **Kernel-checked:** `ToroidalKingsEmptySeam.tiling_free_identity`
  identifies the placement count at $m$ with the free king count at
  $m-1$. The separate conventional-partition interpretation of
  `tilingBlocks` remains **open**.
- **Open:** quantitative convergence rates, numerical certification of
  the constant, and extensions to other tile sets or graphs are not
  established by these declarations.

The free-board entropy, maximum-versus-total comparison and tiling
correspondence retain their cited prior-literature credit. The formal
conclusion supplies the exact all-square toroidal assertion within
the stated placement encoding.

## Escape audit

The four-slot escape audit for the three source modules is unfinished
under the [linked issue](https://github.com/the-omega-institute/trureturing/issues/27011#issuecomment-6671075953).
The native registration assessment fails with
`contract.decode_failed` / `contract.discovery:rigid_universes`. No Reg
client or current validated binding is delivered, and no
`declared_validated` registration is claimed.
