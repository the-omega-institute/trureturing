# Intervention-specific exogenous locality

## Abstract

Parent-indexed evaluation traces induce conservative source supports for finite counterfactual queries. Constant interventions remove dependencies, and source restriction preserves each certified query.

**Definition 1.1 (Local exogenous-coordinate contract).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.ExogenousLocality`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.ExogenousLocality` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For fixed parent values, each equation satisfies the pinned Mathlib DependsOn predicate on its declared source set. No distributional independence is assumed.

**Definition 1.2 (Dependency transfer at one equation).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.equationSupport`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.equationSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A constant intervention has empty incoming support. Otherwise the transfer unions local exogenous coordinates with current supports of declared parents.

**Definition 1.3 (Coordinatewise support update).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.stepSupport`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.stepSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support map changes at exactly the coordinate changed by the canonical structural evaluation step.

**Definition 1.4 (Support propagation along the trace).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.traceSupport`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.traceSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transfer follows the supplied finite evaluation list. The result is a sound upper approximation, rather than a minimal essential-variable set.

**Definition 1.5 (Reuse the unique structural response).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.evaluatedResponse`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.evaluatedResponse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The response is selected from the existing parent-ordered evaluation theorem. No alternative evaluator is introduced.

**Theorem 1.6 (Bind the readout to canonical semantics).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.evaluatedResponse_spec`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.evaluatedResponse_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected response satisfies the existing EvaluationWitness relation at the original initial state.

**Definition 1.7 (Account for all initial-state dependencies).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.compiledSupport`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.compiledSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Initialization starts with all source coordinates admitted. Consequently arbitrary exogenous dependence in model.initial is included in the soundness argument.

**Theorem 1.8 (Soundness on the full exogenous assignment space).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.evaluatedResponse_dependsOn`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.evaluatedResponse_dependsOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Trace induction proves that agreeing on the compiled coordinates forces agreement of the evaluated intervention response.

**Theorem 1.9 (Added constant interventions shrink supports).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.compiledSupport_antitone_intervention`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.compiledSupport_antitone_intervention` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Enlarging the intervention set can only remove compiled dependencies. Query values and identified intervals are not asserted to be monotone.

**Definition 1.10 (Union supports across queried worlds).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualSupport`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite family of intervention queries reads the union of its intervention-specific supports.

**Definition 1.11 (One source assignment for all worlds).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualReadout`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All potential outcomes are evaluated from the same exogenous assignment. Cross-world coupling is preserved.

**Theorem 1.12 (Joint counterfactual locality).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualReadout_dependsOn`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualReadout_dependsOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every coordinate of the finite readout is constant on fibers of the union-support restriction.

**Theorem 1.13 (Query-preserving source restriction).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualEvent_factorsThrough`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualEvent_factorsThrough` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any Boolean event on the readout factors through coordinate restriction using Mathlib FactorsThrough. This is a semantic descent theorem, not a finite novelty score or catalog-admission claim.

**Theorem 1.14 (Remove a shared root by intervention).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.fork_support_cut_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.fork_support_cut_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the four-node fork, fixing treatment leaves a common-root source in both outcome supports. Fixing the common root as well leaves the two separate local outcome sources.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.ExogenousLocality`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.compiledSupport`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.compiledSupport_antitone_intervention`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualEvent_factorsThrough`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualReadout`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualReadout_dependsOn`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.counterfactualSupport`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.equationSupport`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.evaluatedResponse`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.evaluatedResponse_dependsOn`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.evaluatedResponse_spec`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.fork_support_cut_certificate`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.stepSupport`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality.traceSupport`
- Dependency: [D5/S3/ConceptDynamics/Causal/ParentOrderedStructuralEvaluationSemantics](../Causal/ParentOrderedStructuralEvaluationSemantics.md)
