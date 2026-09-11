# Hidden Archive and Temporal Domain

## Abstract

An inactive archived occurrence preserves every current attribute and both spatial charges, while changing the domain of temporal composition.

**Definition 1.1 (The spatial readout has two finite-support coordinates).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.pi`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.pi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first coordinate sums signed point masses over the entire current region. The second sums them over the selected occurrences. Each mass is placed at the event's actual integer spatial position.

**Definition 1.2 (One new occurrence extends the literal archive of U).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.U_old`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.U_old` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

U is the canonical representative of one in dimension three. The extended archive inserts exactly the fresh HF name eventName 1 true. Its time is two, its position is zero, its sign is positive and its source is leaf nine. Causality remains empty. The current and selected occurrences retain their HF names and all their attributes, including time and source.

**Definition 1.3 (A universal temporal-domain preservation claim).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.CurrentSpatialProjectionPreservesTemporalDomains`

*Formalization.* `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.CurrentSpatialProjectionPreservesTemporalDomains` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim quantifies over all balanced rich representations in dimension three and every fixed balanced right operand. It asserts that equal double spatial readouts give equivalent full-archive temporal guards.

**Theorem 1.4 (Unchanged current data coexist with different temporal domains).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.hidden_archive_preserves_current_changes_temporal_domain`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.hidden_archive_preserves_current_changes_temporal_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem supplies an archive embedding that is the identity on HF names, literal equality of current and selected name sets, and equality of all current attributes. The added occurrence lies in neither current set nor selection. Both representations are balanced and have spatial readout zero paired with the unit point mass at zero. Fixing the right operand to the time-one shift of U, composition with U is legal and reads two. The explicit time-two added event and time-one right event violate the extended archive's guard. Temporal composition requires a guard proof, so the illegal branch has no assigned output.

**Theorem 1.5 (Spatial projection does not preserve temporal-composition domains).**

Lean statement: `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.current_spatial_projection_domain_refutation`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.current_spatial_projection_domain_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the universal claim to the complete witness contradicts its failed full-archive guard. Retaining all current event times also fails to recover this domain difference.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.CurrentSpatialProjectionPreservesTemporalDomains`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.U_old`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.current_spatial_projection_domain_refutation`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.hidden_archive_preserves_current_changes_temporal_domain`
- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.pi`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives](IntegerRepresentatives.md)
- Dependency: [D5/S3/ConceptDynamics/Spacetime/TemporalComposition](TemporalComposition.md)
