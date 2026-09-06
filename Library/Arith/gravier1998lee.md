---
bibkey: gravier1998lee
authors: Sylvain Gravier and Michel Mollard and Charles Payan
year: 1998
title: On the Non-existence of 3-Dimensional Tiling in the Lee Metric
doi: 10.1006/eujc.1998.0211
claim: The lattice obstruction leeBallTwo_lattice_obstruction only; there is no lattice tiling of Z cubed by the radius-two Lee ball, equivalently no additive subgroup of index 25 has a quotient map injective on that ball.
strata_touched:
  - D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction
license: citation-only
triage: anchor
---

# On the Non-existence of 3-Dimensional Tiling in the Lee Metric

Gravier, Mollard, and Payan, European Journal of Combinatorics 19(5),
567-572 (1998), provide the literature anchor for the three-dimensional
Lee-tiling obstruction. The claim used here is its radius-two lattice case.
The radius-two Lee ball consists of the integer triples whose sum of absolute
coordinates is at most two and has 25 points. A lattice tiling would make
these points distinct representatives of an index-25 additive quotient.

This note attests only `leeBallTwo_lattice_obstruction` in
`D5/S3/Arith/Coding/LeeBallTwoLatticeObstruction`. The ball definition, its
membership characterization and cardinality, the second and fourth moments,
the two finite-group readout obstructions, and the order-25 classification
are independently derived proof ingredients tagged FromRepo. They are not
attested by this note. The identities with coefficients 18, 30, and 12 are
verified in Lean, and the group classification uses pinned Mathlib.

Leung and Zhou subsequently proved the radius-two lattice obstruction for
every dimension n at least three: Journal of Combinatorial Theory, Series A
171, article 105157 (2020), DOI `10.1016/j.jcta.2019.105157`,
arXiv:1808.08520. That broader result is context, not the scope of this module.

The formal module asserts nothing about non-lattice tilings, other
dimensions, or other radii. Literature attests the known result and its
scope; it is not a Lean proof dependency.

## Verification

- 2026-09-06 (Asia/Singapore): `HEAD https://doi.org/10.1006/eujc.1998.0211`
  returned HTTP 302 to Elsevier's record for PII S0195669898902116; following
  the redirect returned HTTP 200.
- Crossref's `/works/10.1006/eujc.1998.0211` returned the matching title,
  authors S. Gravier, M. Mollard, C. Payan, July 1998 publication date,
  volume 19, issue 5, and pages 567-572.
- The v2 implementation rechecked Crossref's matching 1998 bibliographic
  record and arXiv:1808.08520, whose abstract states the radius-two lattice
  obstruction for every dimension n at least three and whose journal record
  gives the 2020 publication and DOI. Exact helper numbering in the 1998
  article is not claimed or verified here.

## Verified locator

- DOI: https://doi.org/10.1006/eujc.1998.0211
- https://doi.org/10.1016/j.jcta.2019.105157
- https://arxiv.org/abs/1808.08520
