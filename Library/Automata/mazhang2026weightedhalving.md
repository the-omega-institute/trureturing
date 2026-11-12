---
bibkey: mazhang2026weightedhalving
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)"
doi: null
url: https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b
claim: "Actual halving-list length and weight profiles, nonregularity over nonzero commutative rings, power-of-two representation bases and specialized statistical consequences."
strata_touched:
  - D5/S1/Recurrence/Partitions/HalvingPartitionProfile
  - D5/S1/Recurrence/Partitions/HalvingPartitionWeights
  - D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity
  - D5/S1/Recurrence/Partitions/HalvingPartitionGrowth
  - D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity
  - D5/S1/Recurrence/Partitions/HalvingPartitionStatistics
  - D5/S1/Recurrence/Partitions/HalvingPartitionDilation
  - D5/S1/Recurrence/Partitions/HalvingPartitionOneZero
  - D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit
license: CC-BY-4.0
triage: anchor
---

# Weighted halving partitions

The written source is the 7 November 2026 note by **Haobo Ma, then Wenlin Zhang**,
released under CC BY 4.0. Its exact TeX has SHA-256
`97948e8aec759bdfe8cd8efc00a365dce3678c3d5f5e858d85b9b4163ea26405`.
The earlier unweighted primary has SHA-256
`4d8f3764122e0bb658edd906db2d78e0880b9b54e0b6687e4cff57b79e6c1d20`.
These are scientific source identities, not formal acceptance receipts.

The count uses actual positive ordered lists of total n, with virtual predecessor
n, value-set halves and all repeated terminal ones. The weight is the number of
integer digits p-2q+1 equal to one; the parameter can be any element of any
nonzero commutative unital ring, including zero and nonunits.

The fixed-length enumeration is credited to Alekseyev, Theorem 5; even dilation
to his Lemma 2; and the one-missing-bit formula underlying the fixed-bit maximum
lower bound to his Corollary 15. OEIS A349552 was introduced by C. Kimberling;
A. P. Heinz contributed its power-of-two and Mersenne formulas. These antecedents
are not claimed as new. The adopted automata sources retain their atlas-lean
license and the pinned Mathlib license.

The supplied and freshly rerun checkers are finite exact experiments. They do
not establish the universally quantified ring, base, length or machine results.
The general deficit digit formula, exact fixed-bit maximum, general weighted
coefficient formula, partitions using other division bases, A349553 minimal
inputs and general-input unimodality remain outside the proved claims.

## Verified locator

Task source release:
https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b

The release's `note.tex` is the entire weighted note, 18,632 bytes, SHA-256
`97948e8aec759bdfe8cd8efc00a365dce3678c3d5f5e858d85b9b4163ea26405`,
byte-identical to the supplied 7 November source. This is a private task
deliverable locator; it is not a claim of scientific publication. DOI: null.

The precise TeX locators are `lem:profile` / `eq:polynomial` / `eq:count`
in Section 2, `cor:consequences`, `cor:deficit` and `cor:maximum` in that
section, `eq:recurrence` and `cor:automatic` in Section 3, and
`thm:weighted` / `eq:weighted` / `cor:bases` in Section 4. Section 5 records
the verification scope and remaining boundaries.
