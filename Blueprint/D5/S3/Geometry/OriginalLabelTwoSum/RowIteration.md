# RowIteration

## Abstract

Coupled original path-row substitutions recursively construct native certificates and critical statistics on arbitrary retained labels.

**Definition 1.1 (renameRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.renameRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.renameRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Indexed path rows transported injectively; chord indices are not discarded.

**Theorem 1.2 (renameRows_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.renameRows_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.renameRows_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Raw root transport preserves VOID, UNIT and every original indexed row.

**Definition 1.3 (appendWheelRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.appendWheelRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.appendWheelRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact coupled row update. Old rows containing e are substituted; old rows avoiding e and every non-interface right chord index are retained.

**Definition 1.4 (RowHistory).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.RowHistory`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.RowHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite coupled row construction with arbitrary retained-edge choices. No parent endpoint, critical formula, collapse or graph substitution is a field.

**Definition 1.5 (rowHistoryCertificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Recursive native main/core lists for the coupled row class. Both lists are those of the real compiler; there is no separate assumed schedule or critical endpoint in this construction.

**Theorem 1.6 (rowHistory_statistics).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistory_statistics`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistory_statistics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At EVERY finite row stage there are exactly two distinct critical faces, each of size 2n+1. This is a row-level statement. Its interpretation for graph data uses the separate graph and physical-history correspondence.

**Definition 1.7 (rowHistoryCriticalSchedule).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCriticalSchedule`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCriticalSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Critical labels are recursively specified from the actual K4 seed and literal wheel label substitution, independently of rowHistoryCertificate.

**Definition 1.8 (rowHistoryVertexSchedule).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryVertexSchedule`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryVertexSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original terminal vertex recursion, starting at the renamed seed 0.

**Theorem 1.9 (rowHistoryCertificate_schedule_data).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_schedule_data`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_schedule_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate's critical labels and vertex satisfy the independent seed recursions; these equations transport the input data in both list inductions.

**Definition 1.10 (rowHistoryMainSchedule).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryMainSchedule`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryMainSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Seed-based all-n main enumeration. The K4 main is an actual reflexive operation, so its pair list is empty even after the original label map. Each attach flatMaps the previous independently enumerated list.

**Definition 1.11 (rowHistorySeparateSchedule).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistorySeparateSchedule`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistorySeparateSchedule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Seed-based all-n core enumeration, including recursively computed critical labels and vertex. Neither attach reads a previous certificate's native pairs.

**Theorem 1.12 (rowHistoryCertificate_main_orderedPairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_main_orderedPairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_main_orderedPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The main induction consumes the previous list equality through the raw wheel substitution, together with the independent critical-label recursion.

**Theorem 1.13 (rowHistoryCertificate_separate_orderedPairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_separate_orderedPairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_separate_orderedPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The separate induction consumes its own previous-list hypothesis, and both critical/vertex transports. It preserves collars/replay/terminal append order.

**Theorem 1.14 (rowHistoryCertificate_expansion).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A certificate consumer keeps BOTH all-n list expansions and the actual whole-endpoint coordinate-fixed homotopy. No graph identification is assumed.

**Theorem 1.15 (rowHistory_fixed_seed_fresh_wheel).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistory_fixed_seed_fresh_wheel`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistory_fixed_seed_fresh_wheel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed K4 seed/fresh-wheel construction consumes both genuine recursive expansions. Actual graph G2/history/closed-chain binding is still separate.

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.RowHistory`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.appendWheelRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.renameRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.renameRows_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_expansion`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_main_orderedPairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_schedule_data`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCertificate_separate_orderedPairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryCriticalSchedule`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryMainSchedule`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistorySeparateSchedule`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistoryVertexSchedule`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistory_fixed_seed_fresh_wheel`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/RowIteration.rowHistory_statistics`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Graph](Graph.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/WheelSupplier](WheelSupplier.md)
