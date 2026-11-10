# CompilerStages

## Abstract

The original filling-main and separate collar stages assemble native lists on their actual computed parent families.

**Definition 1.1 (selectFilling).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.selectFilling`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.selectFilling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Select the actual P0/P1 or Q0/Q1 filling from the original critical-face interface test.

**Definition 1.2 (parentFillingStage).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentFillingStage`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentFillingStage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct the filling-main stage on the ACTUAL parent after child replay. The list is assembled from all P0/P1 lists; its target families are computed.

**Definition 1.3 (parentCollarStage).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentCollarStage`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentCollarStage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct all Q0/Q1 collar lists on Cout ALONE. Every emitted coface is checked against the other collars; the retained parent critical cells are absent from the domain of this Sequence.

**Theorem 1.4 (parentFillingStage_orderedPairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentFillingStage_orderedPairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentFillingStage_orderedPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Global ordered expansion of the filling-main batch. `fibres` is the real cardinality/finite-enumeration comparator, so this records descending critical order rather than an arbitrary permutation.

**Theorem 1.5 (parentCollarStage_orderedPairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentCollarStage_orderedPairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentCollarStage_orderedPairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Global ordered expansion of the collar batch. Its domain is `Cout` alone; the retained critical simplices are not silently inserted into this list.

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentCollarStage`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentCollarStage_orderedPairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentFillingStage`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.parentFillingStage_orderedPairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/CompilerStages.selectFilling`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/ParentFibres](ParentFibres.md)
