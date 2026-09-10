# Finite HF Event Presentations

## Abstract

Finite HF Event Presentations.

**Definition 1.1 (A finite presentation has an exact HF event equivalence).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TaggedPresentation.eventEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/TaggedPresentation.eventEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An injective HF code realizes the actual finite archive. Its inverse recovers every typed event, and archive attributes and order are transported through this same equivalence.

**Theorem 1.2 (Signed charge respects the event equivalence).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TaggedPresentation.charge_map`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/TaggedPresentation.charge_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum over the actual HF event subtype reindexes to the finite presentation. This proves the readout bridge used by the concrete operations; no arithmetic law is assumed as a field.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TaggedPresentation.charge_map`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TaggedPresentation.eventEquiv`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ComplementCharge](ComplementCharge.md)
