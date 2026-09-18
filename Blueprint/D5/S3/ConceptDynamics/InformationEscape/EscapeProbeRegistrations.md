# EscapeProbeRegistrations

## Abstract

Trigger probe: one new public theorem carrying a complete four-slot escape registration.

**Theorem 1.1 (probe_four_slot_true).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probe_four_slot_true`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probe_four_slot_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity readout over Bool never changes a bit; this is the probe theorem.

**Definition 1.2 (probeArena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probeArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probeArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One CUT slot reads a Boolean state and the law fixes the readout at false.

**Theorem 1.3 (probe_bridge).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probe_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probe_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement is equivalent to the arena law of the identity readout.

**Theorem 1.4 (probe_emptyProof).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probe_emptyProof`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probe_emptyProof` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity kernel separates both states, so the closure leaves no residual.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probeArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probe_bridge`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probe_emptyProof`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/EscapeProbeRegistrations.probe_four_slot_true`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/EscapeRecord](EscapeRecord.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates](RegistrationTemplates.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/LayeredCapture](../InformationEscapeHierarchy/LayeredCapture.md)
