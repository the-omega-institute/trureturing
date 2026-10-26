---
bibkey: tengoku2026subsetsums
authors: James Huang, Samuël Borza
year: 2026
title: "Tengoku subset-sum and powerset-map leaves"
doi: null
url: https://github.com/competemath/tengoku/tree/e784113248524aeef7681b0687c722b426c1b115
claim: "subsetSums is the multiset of subset sums; powerset_map_eq commutes the multiset powerset with mapping."
strata_touched:
  - D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums
license: Apache-2.0
triage: anchor
---

# Attributed multiset leaves

At the immutable revision in the URL, `ComplexExponential.lean:120` defines
`subsetSums`, and `SubsetSumPolynomial.lean:77` proves `powerset_map_eq`.
`TengokuSubsetSums` retains this definition and proof, adapting only the imports
and enclosing namespace. The complete upstream LICENSE, NOTICE and
LICENSE-THIRD-PARTY chain is retained under
`docs/reports/licenses/tengoku-subset-sums/`.

The upstream toolchain is Lean 4.34.0-rc2, whereas this repository uses 4.35.0;
direct dependency adoption is incompatible with these pins. Each port is to be
removed when this repository's own pinned Mathlib supplies an equivalent
declaration, with its consumers changed to direct applications of that source.

## Verified locator

The immutable source is https://github.com/competemath/tengoku/tree/e784113248524aeef7681b0687c722b426c1b115.
The attributed leaves are `ComplexExponential.lean:120` (`subsetSums`) and
`SubsetSumPolynomial.lean:77` (`powerset_map_eq`).
