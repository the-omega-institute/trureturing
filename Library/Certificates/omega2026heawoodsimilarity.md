---
bibkey: omega2026heawoodsimilarity
authors: "The Omega Institute repository contributors"
year: 2026
title: "A structural dissociation gain in every connected Heawood double cover"
doi: null
url: https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108
claim: "Every nonzero trace-zero three-by-three matrix over the binary field is similar to one of six specified matrices."
strata_touched:
  - D5/S1/Eigenstructure/BinaryTraceZeroSimilarity
license: Apache-2.0
triage: anchor
---

# The six binary similarity forms

## Verified locator

[Complete algebraic classification, lines 68–108](https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108)

## Statement and scope

The source splits the characteristic polynomial of a trace-zero binary
matrix of size three into four cases and gives six explicit normal forms.
With one-based matrix units, they are
`E12`, `E12+E23`, `diag(1,1,0)`, `diag(1,1,0)+E12`,
`E13+E21+E32`, and `E13+E21+E32+E23`.

The Lean theorem constructs a conjugating unit to a representative in that
order. The supporting Lean modules construct the requisite ordered bases.

## Attribution

Sub-quorum colorings research artifact. Copyright 2026 The Omega Institute
and contributors. The source publishes its [Apache-2.0 license](https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/LICENSE).
The source [NOTICE](../../docs/reports/licenses/subquorum-colorings-NOTICE.txt)
is reproduced in this repository.
