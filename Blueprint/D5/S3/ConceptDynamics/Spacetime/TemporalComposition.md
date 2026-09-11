# Guarded Temporal Composition

## Abstract

Guarded Temporal Composition.

**Theorem 1.1 (The exact temporal guard on HF archives).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TemporalComposition.hf_time_condition_iff`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/TemporalComposition.hf_time_condition_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every archived left event must occur strictly before every archived right event, including inactive events. This condition is necessary and sufficient for the copied absolute times to increase on the constructed relation.

**Theorem 1.2 (The guarded operation adds readouts).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TemporalComposition.q_temporal`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/TemporalComposition.q_temporal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relation adds every old-left to old-right edge and is transitive and irreflexive. The operation preserves absolute times, adds selected and background charges, and preserves balance on its declared domain.

**Theorem 1.3 (An explicit input translation makes composition possible).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/TemporalComposition.guard_of_large_shift`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/TemporalComposition.guard_of_large_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation adds a specified integer to every time in the right input. A finite nonnegative bound gives a sufficiently large shift for any two archives. Empty archives satisfy the guard vacuously; the operation itself performs no translation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TemporalComposition.guard_of_large_shift`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TemporalComposition.hf_time_condition_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/TemporalComposition.q_temporal`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ParallelComposition](ParallelComposition.md)
