# Certificates

## Abstract

Collapse-only main certificates and separate collar/core sequences retain literal critical boundaries.

**Definition 1.1 (facets).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.facets`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.facets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite union of raw simplices, with the empty index family equal to VOID.

**Definition 1.2 (endpoint).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.endpoint`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.endpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For B : Family V and critical : Finset (Finset V), endpoint B critical = B ⊔ facets critical: retain B and adjoin every subface of each critical simplex. Thus endpoint B ∅ = B, since facets ∅ = VOID. In particular endpoint (delta ∅) ∅ = delta ∅ = UNIT, which retains the empty face.

**Definition 1.3 (CriticalData).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.CriticalData`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.CriticalData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact ordinary critical-cell conditions, including ALL proper subfaces.

**Definition 1.4 (Filling).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.Filling`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.Filling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A local filling need not have a contractible collar.

**Definition 1.5 (Certificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.Certificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.Certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A left input carries an actual vertex and ordinary main/core lists.

**Theorem 1.6 (critical_intersection).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.critical_intersection`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.critical_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual literal simplex/core intersection, with the empty face retained.

**Theorem 1.7 (critical_overlap).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.critical_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.critical_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct retained cells meet only in proper boundary faces.

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.Certificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.CriticalData`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.Filling`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.critical_intersection`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.critical_overlap`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.endpoint`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Certificates.facets`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Native](Native.md)
