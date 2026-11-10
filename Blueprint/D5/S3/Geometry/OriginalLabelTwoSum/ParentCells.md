# ParentCells

## Abstract

The original compiler computes its parent core and proves critical nonemptiness, all boundaries, absence and antichains.

**Definition 1.1 (parentCore).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.parentCore`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.parentCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact Cout from the ORIGINAL proof, on the full original parent ground.

**Definition 1.2 (parentCritical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.parentCritical`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.parentCritical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ordered-index provenance is retained by the compiler schedules; this finite set is the actual output critical family, after proving no unwanted inclusions.

**Theorem 1.3 (mem_parentCritical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.mem_parentCritical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.mem_parentCritical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal critical provenance, consumed by the filling endpoint assembly.

**Definition 1.4 (parentCellData).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.parentCellData`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.parentCellData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complete critical-face proof for the COMPUTED Cout. Compiler constructs the main and separate core lists; neither collapse is a hypothesis here.

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.mem_parentCritical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.parentCellData`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.parentCore`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/ParentCells.parentCritical`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Certificates](Certificates.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Rectangles](Rectangles.md)
