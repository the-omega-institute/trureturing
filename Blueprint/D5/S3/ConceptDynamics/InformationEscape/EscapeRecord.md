# EscapeRecord

## Abstract

Escape records close a statement onto an arena law in one direction and certify where information continues to escape.

**Definition 1.1 (EscapePrimitiveRealization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.EscapePrimitiveRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.EscapePrimitiveRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A forward bridge proves that the statement implies the law of the declared realization; equivalence is not claimed, so the unresolved part is recorded separately.

**Definition 1.2 (EscapeResidualWitness).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.EscapeResidualWitness`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.EscapeResidualWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A residual witness is a pair of arena states that the finest listed kernel of a chain leaves unresolved; it names where the closed information keeps escaping.

**Definition 1.3 (EscapeResidualEmpty).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.EscapeResidualEmpty`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.EscapeResidualEmpty` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closure leaves no residual when the finest listed kernel separates every pair.

**Theorem 1.4 (escapeResidualEmpty_iff).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.escapeResidualEmpty_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.escapeResidualEmpty_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No residual holds exactly when the unresolved pair set is empty.

**Theorem 1.5 (escapeResidualEmpty_no_witness).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.escapeResidualEmpty_no_witness`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.escapeResidualEmpty_no_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A chain without residual admits no residual witness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.EscapePrimitiveRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.EscapeResidualEmpty`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.EscapeResidualWitness`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.escapeResidualEmpty_iff`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapeRecord.escapeResidualEmpty_no_witness`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](TheoremUnit.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture](../InformationEscapeHierarchy/LayeredCapture.md)
