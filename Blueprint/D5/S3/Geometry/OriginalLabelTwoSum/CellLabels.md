# CellLabels

## Abstract

Wheel critical labels have a recoverable original-label transform, exact size increment and closed-chain formulas.

**Definition 1.1 (wheelCell).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original wheel transform removes the interface coordinate only when it actually occurs, and uses the new 1-spoke only in that branch.

**Theorem 1.2 (wheelCell_recovery).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The new first spoke distinguishes the two branches and recovers e.

**Theorem 1.3 (wheelCell_card).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact +2 in BOTH branches, including an interface critical singleton.

**Theorem 1.4 (wheelCell_count).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell_count`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No critical-face count is lost to image collisions. This is a consequence of the explicit recovery equation, not a count assumption of the compiler.

**Definition 1.5 (Label).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.Label`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.Label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full supply of original labels; a finite prefix uses only finitely many. No Fintype on this infinite pool is assumed by any native collapse.

**Definition 1.6 (p).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.p`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.p` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full supply of original labels; a finite prefix uses only finitely many. No Fintype on this infinite pool is assumed by any native collapse.

**Definition 1.7 (u).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.u`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.u` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full supply of original labels; a finite prefix uses only finitely many. No Fintype on this infinite pool is assumed by any native collapse.

**Definition 1.8 (v).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.v`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full supply of original labels; a finite prefix uses only finitely many. No Fintype on this infinite pool is assumed by any native collapse.

**Definition 1.9 (r).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.r`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.r` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source index j,k denotes the mathematical label r(j+1,k+1).

**Definition 1.10 (S).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.S`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source index j,k denotes the mathematical label r(j+1,k+1).

**Definition 1.11 (interface).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.interface`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.interface` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source index j,k denotes the mathematical label r(j+1,k+1).

**Definition 1.12 (first).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.first`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.first` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source index j,k denotes the mathematical label r(j+1,k+1).

**Definition 1.13 (second).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.second`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.second` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source index j,k denotes the mathematical label r(j+1,k+1).

**Definition 1.14 (ground).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.ground`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.ground` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Source index j,k denotes the mathematical label r(j+1,k+1).

**Theorem 1.15 (critical_recurrence).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.critical_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.critical_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal closed-chain label formula is consumed by the ORIGINAL conditional critical transform, with no block-diagonal row replacement.

**Theorem 1.16 (critical_sizes).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.critical_sizes`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.critical_sizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite closed prefix has exactly the stated critical sizes. This arithmetic does not instantiate a closed-chain native history or its graph binding.

**Definition 1.17 (rows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.rows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.rows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coupled original chord rows, retained as an ordered list before root union. This is source preparation for the graph-bound iteration, not that theorem.

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.Label`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.S`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.critical_recurrence`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.critical_sizes`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.first`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.ground`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.interface`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.p`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.r`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.rows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.second`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.u`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.v`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell_card`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell_count`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CellLabels.wheelCell_recovery`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Certificates](Certificates.md)
