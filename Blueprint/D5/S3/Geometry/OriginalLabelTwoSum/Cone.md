# Cone

## Abstract

Descending native cone schedules and the genuine terminal Gamma branch handle removal of the left core vertex.

**Definition 1.1 (collapseCone).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Cone.collapseCone`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Cone.collapseCone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every ordinary cone, on the full unchanged original ground, collapses to its actual apex by the descending list of nonempty faces avoiding that apex. 

**Definition 1.2 (terminalGamma).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Cone.terminalGamma`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Cone.terminalGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Terminal p=e branch with X nonempty: run the supplied right Gamma in the Y-piece, fixing the whole delta(X)*E term, before using an original X-apex. 

**Definition 1.3 (terminalAtInterface).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/Cone.terminalAtInterface`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/Cone.terminalAtInterface` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Output type records the computed original vertex, not an assumed endpoint. 

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Cone.collapseCone`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Cone.terminalAtInterface`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/Cone.terminalGamma`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Fibre](Fibre.md)
