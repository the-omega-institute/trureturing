---
slug: mathar-2024-nonbonding-domino-pairs
bibkey: mathar2024nonbonding
doi: null
url: https://arxiv.org/abs/2404.18806v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.result
---

# Mathar's Conjecture 1 on two non-bonding dominoes

## Problem

R. J. Mathar (arXiv:2404.18806, 2024) counts placements of dominoes on an
`r × c` board that are non-bonding: every square of one is at L1 distance at
least 2 from every square of another. They are hard dimers with
nearest-neighbour exclusion. His Conjecture 1 (equation (21)) reads:

> D(r,c,2) = 2c²r² − 2(cr² + c²r) + ½(r² + c²) − 22cr + (59/2)(c + r) − 30;
> r, c ≥ 3.

Issue #11068 fixes the reading. A domino is a set of two board squares at L1
distance 1, and `D(r, c, 2)` counts the sets of two pairwise non-bonding
dominoes. The identity holds in `ℚ` for all `r, c ≥ 3`.

## Motivation

The paper left the formula as a conjecture from its transfer-matrix tables.
`D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.result` proves it
for all `r, c ≥ 3`.

## Gap

Issue #11068 preregisters the proof route and the literature check. arXiv has
only version 1 and no later paper, Semantic Scholar lists no citation, and the
OEIS has no entry for the rows. `not-found-in-searched-scope`.

## Route

1. Every domino is horizontal or vertical and is determined by its anchor
   square.
2. Two distinct dominoes bond exactly when the offset of their anchors lies in
   a finite list:
   - 11 offsets for equal orientations, the equal domino included;
   - 12 offsets for mixed orientations.
3. The ordered anchor pairs with a given offset form a product of two interval
   overlaps. For `r, c ≥ 3` each overlap is linear in `r` or in `c`.
4. Twice `D(r, c, 2)` is the number of ordered non-bonding pairs: `N²` minus
   the 46 offset classes, where `N = r(c − 1) + (r − 1)c`. Summing gives the
   polynomial.

## Falsifier

The proof would fail if a bonded offset were missing from the lists of step 2,
or if an overlap of step 3 were not linear for some `r, c ≥ 3`.

## Evidence

Brute force from the literal definition (#11068):
- the formula matches for all `3 ≤ r, c ≤ 10`;
- it fails for every tested board with `r ≤ 2` or `c ≤ 2`;
- replacing the constant term `−30` by `−29` matches none of the 36 boards
  with `3 ≤ r, c ≤ 8`.

The canonical source is
`D5/S3/StatisticalMechanics/HardCore/NonBondingDominoPairs.lean`. Its public
declarations are `IsDomino`, `NonBonding`, `D2`, `claim`, and `result`.
- Frozen module statement identity: `sha256:f57332fcc4ec0c999803dfb6462e0d206bf0394329542d85010d8b9462d2eadd`.
- Result declaration statement identity: `sha256:9585653f22b4f09cf7b60c60161fab403e11db0867867aec7dc9b02e3747fdae`.
- Freeze event: `sha256:39e23454011ce8257a8f38c9c198c58c5074bdba412f9192c5c6f51b726ac9cb`.

It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture (2024 paper), preregistered in issue #11068
before any Lean. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`. The anchor bijection, the bond-offset classification
and the overlap counts are new propositions on its live path. Admission basis
`open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
