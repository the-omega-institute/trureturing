---
bibkey: fan2026riesz
authors: Qiuling Fan
year: 2026
title: Riesz capacity ratios with negative exponents
doi: 10.48550/arXiv.2609.11186
url: https://arxiv.org/abs/2609.11186v1
claim: Conjecture 5.9 asks whether the three-point negative-exponent Riesz capacity is maximized at the isosceles endpoint of the stated unit-circle motion.
strata_touched:
  - D5/S3/Geometry/Distances/FanCircleCapacity
license: citation-only
triage: anchor
---

# Riesz capacity ratios with negative exponents

Section 1.1 and equation (2) define the positive-order energy as the maximum,
over all probability measures on the set, of the double integral of the
positive real power of Euclidean distance. The associated negative-exponent
Riesz capacity is the reciprocal-exponent power of that energy. For a finite
set, equation (2) writes the same quantity as the full nonnegative mass
simplex sum; zero masses are allowed.

Conjecture 5.9 on printed page 19 fixes two unit-circle points at polar angles
`phi` and `-phi`, with `pi / 2 < phi <= 2 pi / 3`, and moves the third point
through `0 <= psi <= 2 pi - 3 phi`. It asserts that, for every real `r >= 2`,
the capacity is maximized at `psi = 2 pi - 3 phi`, where the two longer chords
are equal. Section 5.4.1 records an unsuccessful approach rather than a proof.

The formal result proves this conjecture with `ProbabilityMeasure` on the
actual subtype of the three complex points. Every such measure is reconstructed
from its three singleton masses, including zero masses, and transported to and
from ambient measures concentrated on the point set. Explicit maximizing masses
identify the attained energy supremum in both optimizer branches.

The three-point quadratic maximum and the real-power concavity calculation are
credited to Clark and Laugesen, *Riesz capacity: monotonicity, continuity,
diameter and volume* (SIAM Journal on Mathematical Analysis,
DOI `10.1137/24M171992X`), Theorem 8 and Section 7 respectively. The unified
positive-part transition and the chord/cotangent derivative comparison along
Fan's fixed-circle path are the repository's synthesis; they are not attributed
to that paper. Together they show that the exact optimizer value is
nondecreasing from `psi` to `2 pi - 3 phi`, and monotonicity of the nonnegative
reciprocal power yields the stated capacity inequality for every real `r >= 2`.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2609.11186
- URL: https://arxiv.org/abs/2609.11186v1
- Version and location: arXiv:2609.11186v1, Sections 1.1, 3, and 5.4,
  especially Conjecture 5.9 and Section 5.4.1.
- Retrieval: the arXiv HTML endpoint returned HTTP 200 on 22 September 2026.

## Formal result

- `D5/S3/Geometry/Distances/FanCircleCapacity.result` proves Conjecture 5.9
  with the source's full real parameter range and all probability measures.
- The kernel statement uses the actual complex point subtype and makes no
  finite-grid, integer-exponent, fixed-pentagon, or positive-mass restriction.
