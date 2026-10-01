---
bibkey: adamaszek2012hardsquares
authors: Michal Adamaszek
year: 2012
title: "Hard squares on cylinders revisited"
doi: null
url: https://arxiv.org/abs/1202.1655v2
claim: "Section 7 defines (k, n)-necklaces, the four pair conditions, and JUMP–TURN–FIX; Conjecture 7.4 asks whether every cycle length in Neck(k, n) divides n−3k."
strata_touched:
  - D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod
license: citation-only
triage: anchor
---

# Adamaszek, hard squares on cylinders

Section 7 assumes that n is an even positive integer and k is a positive integer.
The definition starts on page 12:

> We define a (k, n)-necklace. It is a collection of 2k points (stones) distributed along the circumference of a circle of length n, together with an assignment of a number from {−2, −1, 1, 2} to each of the stones.

> The vector points 1 or 2 units clockwise (positive value) or anti-clockwise (negative value) from each stone and we say a stone faces the direction of its vector.

The four conditions, pages 12–13, are:

> consecutive stones face in opposite directions,

> if two consecutive stones face away from each other then their distance is an odd integer,

> if two consecutive stones face towards each other then their distance plus the lengths of their vectors is an odd integer,

> if two consecutive stones face towards each other then their distance is at least 3; moreover if their distance is exactly 3 then their vectors have length 1.

On page 13:

> We identify (k, n)-necklaces which differ by an isometry of the circle.

> Next we describe a necklace transformation T which takes a (k, n)-necklace and performs the following operations:

> (JUMP) all stones jump as dictated by their vectors,

> (TURN) all stone vectors change according to the rule −2→1, −1→2, 1→−2, 2→−1,

> (FIX) if any two stones find themselves in distance 3 facing each other and any of their vectors has length 2, then adjust the offending vectors by reducing their length to 1.

Definition 7.1 uses isometry classes as vertices and the edges N→TN.
Conjecture 7.4, page 14, states:

> The length of every cycle in the graph Neck(k, n) divides n−3k. In other words, for every (k, n)-necklace N we have Tⁿ⁻³ᵏN = N.

The encoding uses one optional vector at each site of ZMod n, all 2k occupied
sites, clockwise consecutive pairs including the wrap pair, and both rotations
and reflections. Reflection negates the vectors. Integer clockwise gaps follow
from the parity conditions, permitting an integer origin up to rotation.

Theorem 7.5 expresses the denominators of pattern generating functions in terms
of common multiples of necklace cycle lengths. Theorem 7.6 states that
Conjecture 7.4 implies Conjecture 1.4. These generating-function statements are
literature results; their translation into Lean is a separate obligation.

## Verified locator

https://arxiv.org/abs/1202.1655v2 — version 2; Section 7, pages 12–15;
Conjecture 7.4 on page 14. The quotation text is checked against the v2 TeX source
and the printed PDF. This note cites the source and its definitions; the proof
of Conjecture 7.4 is the repository theorem HardSquareNecklacePeriod.result.
