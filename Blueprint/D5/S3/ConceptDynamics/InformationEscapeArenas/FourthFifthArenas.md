# Fourth and Fifth Information-Escape Arenas

## Abstract

Finite typed arenas for contextual meanings and causal models.

**Definition 1.1 (Context finite instance).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextFintype`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite instance obtained through a private equivalence.

**Definition 1.2 (Context decidable equality).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextDecidableEq`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextDecidableEq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A decidable-equality instance obtained through a private equivalence.

**Definition 1.3 (Context readout indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.ContextReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.ContextReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout index type names the context fields, the two fixed-meaning admissions, and their typed axes.

**Definition 1.4 (Context signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed signature exposes the five context parameters as CUT readouts and the two fixed meanings as ADMIT readouts.

**Definition 1.5 (Context-selected fixed-meaning arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The arena packages BinaryInterpretationContext, contextSignature, and the anchor law separating the selected parameters and meanings.

**Theorem 1.6 (The contextArena state space is nondegenerate).**

$$\operatorname{Nondegenerate}(\operatorname{toArena}(contextArena))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextArena_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite arena contains at least two distinct states.

**Definition 1.7 (Causal-model finite instance).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.modelFintype`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.modelFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite instance obtained through a private equivalence.

**Definition 1.8 (Causal-model decidable equality).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.modelDecidableEq`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.modelDecidableEq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A decidable-equality instance obtained through a private equivalence.

**Definition 1.9 (Causal-model readout indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.ModelReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.ModelReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout index type separates intervention behavior from counterfactual behavior.

**Definition 1.10 (Intervention signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.interventionSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.interventionSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The typed signature assigns the Int and CF function types to the two CUT readouts on DeterministicBoolSCM.

**Definition 1.11 (Intervention and counterfactual arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.interventionArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.interventionArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The arena packages DeterministicBoolSCM and requires two models with equal intervention readouts and unequal counterfactual readouts.

**Theorem 1.12 (The interventionArena state space is nondegenerate).**

$$\operatorname{Nondegenerate}(\operatorname{toArena}(interventionArena))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.interventionArena_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite arena contains at least two distinct states.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.ContextReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.ModelReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextArena_nondegenerate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextDecidableEq`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextFintype`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.contextSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.interventionArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.interventionArena_nondegenerate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.interventionSignature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.modelDecidableEq`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.modelFintype`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](../InformationEscape/TheoremUnit.md)
- Dependency: [D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint](../Interpretation/InterpretationFixedPoint.md)
- Dependency: [D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation](../Interventions/InterventionCounterfactualSeparation.md)
