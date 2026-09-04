# End State Omits Preempting Cause Arena

## Abstract

Ordered preemption is expressed through endpoint, cause, admission, and anchor primitives.

**Definition 1.1 (Boolean mechanism equivalence).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.mechanismEquiv`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.mechanismEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence exhaustively identifies the two source mechanisms with Boolean values.

**Definition 1.2 (Finite source mechanisms).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instFintypeMechanism`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instFintypeMechanism` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the finite/decidable-equality instance obtained through a private equivalence.

**Definition 1.3 (Decidable ordered preemption).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instDecidableIsOrderedPreemption`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instDecidableIsOrderedPreemption` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This decidability instance is obtained by unfolding the finite ordered-preemption predicate.

**Definition 1.4 (Preemption readout indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.PreemptionReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.PreemptionReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite index type names the two CUT and two ADMIT readouts.

**Definition 1.5 (Decidable equality for preemption readouts).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instDecidableEqPreemptionReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instDecidableEqPreemptionReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the finite/decidable-equality instance obtained through a private equivalence.

**Definition 1.6 (Finite preemption readouts).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instFintypePreemptionReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instFintypePreemptionReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the finite/decidable-equality instance obtained through a private equivalence.

**Definition 1.7 (Preemption anchor indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.PreemptionAnchor`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.PreemptionAnchor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite anchor type names the two source trace witnesses.

**Definition 1.8 (Decidable equality for preemption anchors).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instDecidableEqPreemptionAnchor`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instDecidableEqPreemptionAnchor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the finite/decidable-equality instance obtained through a private equivalence.

**Definition 1.9 (Finite preemption anchors).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instFintypePreemptionAnchor`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instFintypePreemptionAnchor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the finite/decidable-equality instance obtained through a private equivalence.

**Definition 1.10 (Typed preemption signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.preemptionSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.preemptionSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature assigns endpoint and active-cause CUTs, two Boolean ADMITS, and both trace anchors.

**Definition 1.11 (Frozen preemption statement type).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.EndStateOmitsPreemptingCauseStatement`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.EndStateOmitsPreemptingCauseStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This alias is definitionally the type of the frozen theorem D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause.end_state_omits_preempting_cause.

**Definition 1.12 (Preemption trace arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two CUTs and two coded ADMITS are evaluated at the named trace anchors, including the endpoint-factorization obstruction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.EndStateOmitsPreemptingCauseStatement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.PreemptionAnchor`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.PreemptionReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instDecidableEqPreemptionAnchor`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instDecidableEqPreemptionReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instDecidableIsOrderedPreemption`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instFintypeMechanism`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instFintypePreemptionAnchor`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.instFintypePreemptionReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.mechanismEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/EndStateOmitsPreemptingCause.preemptionSignature`
- Dependency: [D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause](../Attribution/EndStateOmitsPreemptingCause.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](../InformationEscape/TheoremUnit.md)
