---
bibkey: wang2026ktv
authors: Guanyang Wang
year: 2026
title: KTV Proof Formalization
doi: null
url: https://github.com/guanyangwang/ktv-swap-lean/blob/15b5f47c9ac833bfdf99b8b29374af7a678ef4bc/KTV/Johnson/Connectivity.lean#L1394
claim: Simple alternating disagreement-cycle extraction for unequal finite Boolean tables with equal labeled row and column margins.
strata_touched:
  - D5/S3/Combinatorics/Transportation/SupportedCycleSupplier
license: MIT
triage: anchor
---

# Finite Boolean disagreement-cycle extraction

## Verified locator

Guanyang Wang, *KTV Proof Formalization*, immutable revision
`15b5f47c9ac833bfdf99b8b29374af7a678ef4bc`:
https://github.com/guanyangwang/ktv-swap-lean/blob/15b5f47c9ac833bfdf99b8b29374af7a678ef4bc/KTV/Johnson/Connectivity.lean#L1394

The revision's README describes the project as a Lean formalization for
*Spectral Gap for the Binary Fixed-Margin Swap Chain*. The consumed result is
`KTV.Johnson.exists_simple_fixedMarginAlternatingClosedWalk`, beginning at
line 1394 in `KTV/Johnson/Connectivity.lean`, together with its extraction
dependencies in that file and in `KTV/Johnson/BinaryMatrix/Basic.lean` and
`KTV/Johnson/BinaryMatrix/Proposals.lean`.

## Statement correspondence

The upstream theorem assumes an alternating closed walk between two states of
one fixed-margin model. It returns a length at least two, row and column
sequences separately without repetitions below that length, positive diagonal
disagreements, negative shifted disagreements and the negative closing edge.
The local private extraction theorem retains this statement.

The public consumer
`D5/S3/Combinatorics/Transportation/SupportedCycleSupplier.simple_cycle`
starts from unequal states. It uses the consumed upstream
`exists_fixedMarginPositiveDisagreement_iterate_repeat_nat` (line 498),
`fixedMarginPositiveDisagreement_next_ne` (line 442) and
`fixedMarginAlternatingClosedWalkLength_of_positiveDisagreement_cycle`
(line 1515) to supply the closed walk before applying the simple-walk theorem.
Rows and columns are arbitrary finite types with decidable equality and
independent universes; their labeled row and column counts agree individually.
The namespace, module layout, visibility and imports are adapted locally.
This attribution covers the extraction closure used by this consumer. It does
not attribute the arbitrary-support conformal flips or bounded full chain in
`SupportedBooleanCycles` to this source, and supplies no spectral-gap theorem
for that consumer.

## License and dependency boundary

The immutable source's MIT license names Copyright (c) 2026 Guanyang Wang.
The complete notice and license text are retained in
`D5/S3/Combinatorics/Transportation/SupportedCycleSupplier.lean`.

The source pins Lean v4.31.0 and Mathlib
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`; this repository pins Lean v4.35.0
and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The incompatible pins require a source transplant rather than a direct package
import. Replace the transplant with direct imports when this repository's own
pinned Mathlib contains equivalent fixed-margin simple disagreement-cycle
extraction, as specified in the owning Lean source. An unpinned upstream result
does not satisfy that condition.
