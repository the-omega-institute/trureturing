# Rename

## Abstract

Injective original-label transport reuses mathlib complex maps and transports actual native pairs, sequences and fillings.

**Definition 1.1 (renameFamily).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameFamily`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Direct image of raw faces, without adjoining empty to a VOID source. 

**Theorem 1.2 (project_rename).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.project_rename`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Rename.project_rename` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projection agrees exactly with the pinned mathlib image-complex API. 

**Definition 1.3 (renamePair).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renamePair`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renamePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ordinary free pairs transport through an injective label map. Freeness is proved on all cofaces of the mapped ambient, rather than postulated. 

**Definition 1.4 (renameSequence).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameSequence`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Recursive transport of the ACTUAL native list. 

**Theorem 1.5 (renameSequence_pairs).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameSequence_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameSequence_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact ordered coverage of the transported ordinary pairs. 

**Theorem 1.6 (rename_operations).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.rename_operations`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Rename.rename_operations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Simplex, intersections and endpoint families are transported literally. 

**Definition 1.7 (renameFilling).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameFilling`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameFilling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A local filling can be installed on any fresh original labels. 

**Definition 1.8 (renameCertificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameCertificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Absolute certificates transport with every original ground/ghost label. 

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.project_rename`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameCertificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameFamily`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameFilling`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renamePair`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameSequence`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.renameSequence_pairs`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Rename.rename_operations`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Certificates](Certificates.md)
