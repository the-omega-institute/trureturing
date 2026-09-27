# DependentFamily

## Abstract

A generic dependent-family contract separates typed readouts from source binding and audit proofs.

**Definition 1.1 (Dependent signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Signature`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Signature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five universe parameters t, s, r, o and a retain arbitrary Params, parameter-dependent State and role-and-parameter-dependent Output types. Only Role and Anchor carry finite enumerations; Role is nonempty. No finiteness or decidable equality is required of parameters, states or outputs.

**Definition 1.2 (Readouts and anchors).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Realization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Realization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A realization supplies one typed readout for every role and parameter, and one state in every parameter fiber for each anchor. These are mathematical operands, not registration evidence.

**Definition 1.3 (Shared constructor).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.realize`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.realize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructor stores the supplied readout and anchor families unchanged. Reg/Support/DependentFamily enrolls this common template; constructing a realization alone grants no enrollment.

**Definition 1.4 (Law over a realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Arena`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Arena` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An arena pairs a signature with a proposition-valued Law on its realizations. Consumer family definitions retain the complete source statement at the actual realization, including dependent hypotheses and conclusions.

**Definition 1.5 (Whole-family variation).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Variation`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Variation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Variation requires Law actual and a realization bad with not Law bad. The intervention varies a whole family; it need not vary in every fiber, so degenerate fibers remain in the domain.

**Definition 1.6 (Live roles and anchors).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Sensitivity`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Sensitivity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each role, a law-breaking realization must keep every other readout and all anchors fixed at actual. For each anchor, a law-breaking realization must keep all readouts and every other anchor fixed. Empty anchor types make only the anchor clause vacuous.

**Definition 1.7 (Nonconstant actual observations).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.ObservationalDependence`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.ObservationalDependence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each role must have a parameter and two states in that same fiber with different actual outputs. Hypothetical variation cannot justify a constant actual readout; this requirement does not assert variation in every fiber.

**Definition 1.8 (Proof contract and source boundary).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Registration`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Registration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The record requires an actual realization, an equivalence between the supplied statement and Law actual, variation, sensitivity and observational dependence. Source selection separately ties that statement to the original compiler declaration: coordinates, scoped occurrences, dependent binders, rigid universes and full statement reconstruction remain obligations of the source-binding consumer. A record alone does not establish source fidelity or enrollment.

These are repository-derived schema definitions under Scribe provenance, with no novelty, coverage or freeze claim. Reg carries the audit proofs. A literal open residual records unknown residual information; it proves neither infinity, undecidability nor completeness and discharges none of the proof or binding obligations.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Arena`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.ObservationalDependence`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Realization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Registration`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Sensitivity`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Signature`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.Variation`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/DependentFamily.realize`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena](../InformationEscapeHierarchy/StructuralArena.md)
