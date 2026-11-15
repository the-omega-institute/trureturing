---
bibkey: lafreniere2025intervalclosed
authors: Nadia Lafrenière, Joel Brewster Lewis, Erin McNicholas, Jessica Striker, Amanda Welch
year: 2025
title: "Interval-closed set rowmotion and homomesy on products of two chains"
doi: 10.48550/arXiv.2505.04000
url: https://arxiv.org/abs/2505.04000v1
claim: "Theorem 1.1 and its proof give the finite-poset interval-closed rowmotion image formula; Conjecture 4.2 restates the earlier max-minus-min homomesy conjecture for products of two chains, and the paper proves a separate signed-cardinality result."
strata_touched:
  - D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy
  - D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation
  - D5/S3/Combinatorics/Geometry/RowmotionGlobalFormula
license: citation-only
triage: anchor
---

# Interval-closed set rowmotion and homomesy on products of two chains

The follow-up studies interval-closed rowmotion and its orbits on products of
two chains. Conjecture 4.2 explicitly cites the earlier max-minus-min
homomesy conjecture. Its separate signed-cardinality homomesy theorem is not
used as the target of the repository result.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2505.04000
- URL: https://arxiv.org/abs/2505.04000v1
- Version and location: arXiv:2505.04000v1, Theorem 1.1 and its proof;
  Conjecture 4.2 and Remark 4.3.

## Global image formula

For an interval-closed subset I of a finite poset, let C be the minimal
elements of the upper closure of I outside I, and let H be the minimal
elements of I that lie in the lower closure of C. The rowmotion image is the
union of the points incomparable with every member of C outside I and the
lower closure of C outside the lower closure of H. These are the ceiling,
lower boundary, incomparable region and image formula used in
`RowmotionGlobalFormula`.

The repository's [Rowmotion endpoint transport](../../docs/develop/theory/ROWMOTION_ENDPOINT_TRANSPORT.md),
equation (2.3), attributes this exact identity to Theorem 1.1 and its proof.
This locator is supported by that repository source; no separate inspection
of the external paper is asserted here. The mathematical attribution is
distinct from the Lean implementation's Columbus Labs adaptation attribution
and MIT license, which remain in the Lean source.

## Signed-cardinality scope

Theorem 1.3 proves the m = 2 clause for odd n. Remark 3.31 (p. 40)
retains the m = 3 clause in the sentence: “As noted in [11, Conjecture 4.12],
the signed cardinality statistics seems to be homomesic under rowmotion for
[3]×[n] when n is even.” The [3]×[12] refutation concerns that conjectural
clause; it does not negate the proved two-row result.
