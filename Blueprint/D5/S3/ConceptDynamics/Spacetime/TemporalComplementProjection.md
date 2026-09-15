# Temporal Complement Projection

## Abstract

Temporal composition transports event complements componentwise and preserves the induced signed-charge projection.

**Theorem 1.1 (Complement of a temporal selection projects to component complements).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.complement_selection_projection`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.complement_selection_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a guarded temporal composition of contexts c and e, and selections a and b, the complement in the joined current region is exactly the disjoint sum of c's complement of a and e's complement of b, transported by the canonical event equivalence. This is a finite event-set identity and does not assert coverage of the broader temporal-profile atom.

**Theorem 1.2 (Signed charge projects through temporal complement).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.temporal_complement_projection`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.temporal_complement_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readout of the joined complement equals the sum of the two component complement readouts. The equality follows for arbitrary finite contexts from the componentwise set projection and the finite charge decomposition.

**Theorem 1.3 (Projection and discrete temporal separation).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.temporal_complement_projection_spec`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.temporal_complement_projection_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The packaged projection also records the integer one-step gap forced by the strict archive-time guard for every left and right archived event. This arithmetic consequence is part of the module's content witness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.complement_selection_projection`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.temporal_complement_projection`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection.temporal_complement_projection_spec`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TemporalComposition](TemporalComposition.md)
