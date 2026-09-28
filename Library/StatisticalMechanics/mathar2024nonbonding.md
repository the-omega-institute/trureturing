---
bibkey: mathar2024nonbonding
authors: Richard J. Mathar
year: 2024
title: "Bivariate Generating Functions Enumerating Non-Bonding Dominoes on Rectangular Boards"
doi: null
url: https://arxiv.org/abs/2404.18806v1
claim: "Two dominoes are non-bonding when they share at most one corner point, i.e. every square of one has L1 distance at least 2 from every square of the other; D(r,c,d) counts arrangements of d non-overlapping non-bonding dominoes on an r x c board. Conjecture 1 (equation (21)): D(r,c,2) = 2c^2r^2 - 2(cr^2 + c^2r) + (r^2 + c^2)/2 - 22cr + (59/2)(c + r) - 30 for r, c >= 3."
strata_touched:
  - D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs
license: citation-only
triage: anchor
---

# Mathar 2024, non-bonding dominoes

R. J. Mathar, "Bivariate Generating Functions Enumerating Non-Bonding
Dominoes on Rectangular Boards", arXiv:2404.18806v1 (2024-04-29, math.CO).

The paper (§1) defines:

> We call two dominoes non-bonding (or non-adjacent) when they do not share
> any of their 7 (1 internal + 6 perimeter) edges, that is, if they share at
> most one point at one of the four corners. The same criterion is that the
> distance of any of the two squares in a domino has minimum L1 (Manhattan)
> distance of 2 to any other square in a different domino.

> Definition 1. D(r,c,d) is the number of arrangements of d non-overlapping,
> non-bonding dominoes on a r×c rectangular square grid.

It then computes rational bivariate generating functions by the transfer
matrix method for boards with up to six rows or columns. From the resulting
tables (p. 11) it records:

> Conjecture 1. (21) D(r,c,2) = 2c²r² − 2(cr² + c²r) + ½(r² + c²) − 22cr +
> (59/2)(c + r) − 30; r, c ≥ 3.

The paper compares its tiling to the 2×2 unit cell of surface physics. The
model is a hard-core lattice gas of dimers with nearest-neighbour exclusion.

## Verified locator

- URL: https://arxiv.org/abs/2404.18806v1 (version 1, the only version,
  submitted 2024-04-29; Conjecture 1 is equation (21) on page 11; full text
  retrieved 2026-09-28).
