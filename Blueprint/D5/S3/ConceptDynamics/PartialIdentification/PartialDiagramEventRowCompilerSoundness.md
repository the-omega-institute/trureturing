# Partial-Diagram Event-Row Compiler Soundness

## Abstract

Observational, interventional, and counterfactual event probabilities compile to exact rational rows over admissible graph-completion and response-signature atoms.

The finite carrier records both a candidate graph completion and a deterministic response signature. Structural rows enforce nonnegativity, normalization, required and forbidden edge assertions, and compatibility with the query-implied causal order.

Every supplied causal event is represented by a zero-one indicator on this joint carrier. Paired upper and lower rows enforce equality between its finite event mass and the nominated rational probability.

Event kind and constraint provenance are stored separately. Observational, interventional, and counterfactual describe event semantics. Data, structural, and sensitivity describe why a numerical equality may be imposed.

**Theorem 1.1 (Generated rows exactly characterize admissible event-constrained laws).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.feasible_iff_event_constrained_completion_law`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.feasible_iff_event_constrained_completion_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A mass vector is feasible for the compiled program exactly when it is nonnegative, normalized, supported on graph completions satisfying all diagram and query-order conditions, and realizes every supplied event target.

**Theorem 1.2 (Joint response pushforward preserves every Boolean event probability).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.joint_event_mass_pushforward`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.joint_event_mass_pushforward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pushing a finite exogenous law to completion-signature atoms and then evaluating an event gives exactly the probability obtained by evaluating that event directly on the original exogenous states.

**Theorem 1.3 (Every compiled event target has a canonical finite realization).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.compiled_event_targets_have_identity_realization`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.compiled_event_targets_have_identity_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint atom carrier itself serves as an exogenous state space, so every feasible compiled law realizes all observational, interventional, and counterfactual event equalities in one finite model.

**Theorem 1.4 (Additional partial-diagram information shrinks the event-constrained feasible set).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.feasible_antitone_under_diagram_refinement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.feasible_antitone_under_diagram_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When a stronger partial diagram retains every assertion of a weaker diagram, every strongly feasible event law is also feasible for the weaker compiler while all statistical event rows remain unchanged.

**Theorem 1.5 (Weaker-diagram lower certificates remain valid after refinement).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.lower_bound_survives_diagram_refinement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.lower_bound_survives_diagram_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational dual lower-bound certificate for the weaker event compiler remains valid for every mass feasible under stronger graph information. The corresponding upper-bound transport is proved symmetrically.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.compiled_event_targets_have_identity_realization`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.feasible_antitone_under_diagram_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.feasible_iff_event_constrained_completion_law`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.joint_event_mass_pushforward`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramEventRowCompilerSoundness.lower_bound_survives_diagram_refinement`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/PartialDiagramConstraintCompilerSoundness](PartialDiagramConstraintCompilerSoundness.md)
