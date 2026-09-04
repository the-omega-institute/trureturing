# Static Exact Experiment Design Arena

## Abstract

The static exact-design law is carried by two typed Boolean CUT readouts.

**Definition 1.1 (Static readout indices).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.StaticReadout`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.StaticReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The readout index type is the two-element finite type of static experiments.

**Definition 1.2 (Static experiment signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.staticSignature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.staticSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signature assigns a Boolean output to each of the two CUT readout indices.

**Definition 1.3 (Frozen static exact-design statement).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.StaticExactDesignStatement`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.StaticExactDesignStatement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This alias is definitionally the type of the frozen theorem D5/S3/ConceptDynamics/ExperimentDesign/StaticExactExperimentDesign.static_exact_design.

**Definition 1.4 (Static exact-experiment arena).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.staticExactExperimentArena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.staticExactExperimentArena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The law reproduces individual failure, joint injectivity, and minimal selection using the two realization slots.

**Theorem 1.5 (Static exact-experiment arena is nondegenerate).**

$$\operatorname{Nondegenerate}(\operatorname{toArena}(staticExactExperimentArena))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.staticExactExperimentArena_nondegenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three-element source carrier contains a pair of distinct models.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.StaticExactDesignStatement`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.StaticReadout`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.staticExactExperimentArena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.staticExactExperimentArena_nondegenerate`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.staticSignature`
- Dependency: [D5/S3/ConceptDynamics/ExperimentDesign/StaticExactExperimentDesign](../ExperimentDesign/StaticExactExperimentDesign.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/TheoremUnit](../InformationEscape/TheoremUnit.md)
