# Batch

## Abstract

Finite noninterfering critical fibres produce actual native sequences with exact ordered pair coverage.

**Definition 1.1 (fibreLayers).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Batch.fibreLayers`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Batch.fibreLayers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal union of indexed fibre families. Repeated indices are not needed. 

**Theorem 1.2 (mem_fibreLayers).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Batch.mem_fibreLayers`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Batch.mem_fibreLayers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership retains the actual fibre index and local face. 

**Definition 1.3 (batchFibre).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Batch.batchFibre`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Batch.batchFibre` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite batch, with actual evolving base (finished N-fibres and unfinished M-fibres). The pair list is precisely the concatenation of the lifted local lists, in the supplied finite index order. 

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Batch.batchFibre`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Batch.fibreLayers`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Batch.mem_fibreLayers`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Fibre](Fibre.md)
