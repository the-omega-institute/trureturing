# Native

## Abstract

Descending finite fibres emit existing native free pairs with exact evolving endpoints and ordered coverage.

**Definition 1.1 (cut).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Removing upper ideals is always downward closed; freeness is proved before using it as the retained complex of an ordinary pair.

**Theorem 1.2 (cut_empty).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing upper ideals is always downward closed; freeness is proved before using it as the retained complex of an ordinary pair.

**Theorem 1.3 (cut_cut).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing upper ideals is always downward closed; freeness is proved before using it as the retained complex of an ordinary pair.

**Definition 1.4 (emitPair).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.emitPair`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Native.emitPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Populate the actual native pair, using the whole current raw family.

**Theorem 1.5 (emitPair_retained).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.emitPair_retained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Native.emitPair_retained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality is literal deletion of the upper ideal of the lower face.

**Definition 1.6 (fibreBefore).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.fibreBefore`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Native.fibreBefore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Label-order tie break. The finite enumeration is fixed once per ambient Fintype instance; cardinality is always the primary comparison.

**Definition 1.7 (fibres).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.fibres`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Native.fibres` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual terminating merge-sort, not an assumed fibre schedule.

**Theorem 1.8 (fibres_spec).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.fibres_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Native.fibres_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual terminating merge-sort, not an assumed fibre schedule.

**Definition 1.9 (rectangle).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.rectangle`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Native.rectangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Public rectangle endpoint and genuine ordered native list.

**Theorem 1.10 (rectangle_order).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.rectangle_order`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Native.rectangle_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The list statement refers to the real pair extraction, and contains no external pair schedule assumption.

**Theorem 1.11 (cut_fixed).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixed coordinate consequence of the EXISTING Sequence homotopy.

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut_cut`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut_empty`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.cut_fixed`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.emitPair`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.emitPair_retained`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.fibreBefore`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.fibres`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.fibres_spec`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.rectangle`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Native.rectangle_order`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Raw](Raw.md)
