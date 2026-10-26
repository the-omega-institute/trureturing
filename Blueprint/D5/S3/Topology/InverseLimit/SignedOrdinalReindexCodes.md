# Birth-local reservation coding

## Abstract

Birth-local first-reservation codes and cofinal hole colors

Tags consist of all ordinary labels and precisely the delayed triples valid on one whole birth pack. The code uses the fixed ordinal reservation bijection and this birth alone. It does not consult a later history state. Ordinary zero remains zero; every other tag uses its first syntactically valid reservation. The second reservation supplies cofinal colors for the labels omitted by the code image.

**Theorem 1.1 (Distinct tags have distinct task syntax).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.taskSyntax_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.taskSyntax_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordinary labels and intrinsically valid delayed triples have distinct fixed task reservations. The validity proof in a delayed tag does not distinguish tags with the same triple.

**Theorem 1.2 (Every tag has cofinal valid reservations).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.occurs_cofinal`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.occurs_cofinal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any fixed birth row, intrinsic tag and ordinal bound, a later reservation has that tag and meets all ordinary or delayed domain inequalities.

**Theorem 1.3 (Ordinary zero retains zero).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinguished ordinary label zero has code zero.

**Theorem 1.4 (Nonzero codes are valid occurrences).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_occurs`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_occurs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every tag other than ordinary zero is coded by a reservation of its exact syntax satisfying the original stage domain conditions.

**Theorem 1.5 (The birth row precedes every nonzero code).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.row_le_code`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.row_le_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero tag code is at least its birth row, hence has positive ordinal value.

**Theorem 1.6 (Original measure labels precede their codes).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.target_le_code`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.target_le_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an ordinary tag the original measure label is its ordinary label. For a delayed tag it is the target label. Each is at most the new code.

**Theorem 1.7 (The first code precedes every occurrence).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_le_occurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_le_occurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every syntactically matching valid reservation lies at or above the code. Ordinary zero satisfies the same bound because its code is zero.

**Theorem 1.8 (Only ordinary zero has code zero).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive birth-row bounds separate every other tag code from zero.

**Theorem 1.9 (Tag coding is injective).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of two nonzero codes forces equality of the unique task syntax reserved there. The zero case is separated by the birth-row bound.

**Theorem 1.10 (Two nested reservation tasks are cofinal).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.double_reservation_cofinal`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.double_reservation_cofinal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given two tasks and any bound, there is a later stage whose first reservation task is the outer task and whose residual ordinal has the inner task. The nested inverse reservation map is injective; a bound would inject all countable ordinals into a countable initial segment.

**Theorem 1.11 (Colored ordinary indices stay within the stage).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.ordinaryIndex_le`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.ordinaryIndex_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An ordinary zero event uses its second reservation color only when that color lies within the stage and is zero or outside the code image. Other ordinary labels use their first codes. Every valid ordinary occurrence therefore receives an index at most its stage.

**Theorem 1.12 (Every hole and zero occurs cofinally).**

Lean statement: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.hole_cofinal`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.hole_cofinal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every label outside the code image, and also for zero, there are cofinally many valid ordinary zero reservations above both the row and the label whose ordinary index equals that label. The two nested reservation tasks prescribe the row event and its color independently.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_eq_zero_iff`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_injective`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_le_occurrence`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_occurs`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.code_zero`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.double_reservation_cofinal`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.hole_cofinal`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.occurs_cofinal`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.ordinaryIndex_le`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.row_le_code`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.target_le_code`
- Truth anchor: `D5/S3/Topology/InverseLimit/SignedOrdinalReindexCodes.taskSyntax_injective`
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalHistory](SignedOrdinalHistory.md)
