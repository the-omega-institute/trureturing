# Query-Implied Causal Order

## Abstract

Counterfactual intervention atoms generate strict causal-order obligations and expose cyclic query inconsistency.

A counterfactual atom names an outcome and a finite intervention set. Every nontrivial intervened coordinate generates a precedence obligation from the intervened coordinate to the atom's outcome.

A query is order-compatible when one strict causal order respects every generated obligation. Asymmetry immediately rejects reciprocal requirements, which cannot occur in one recursive causal ordering.

The list-order adapter targets the canonical Before relation already used by finite structural evaluation in this causal lane. LP sharpness and invariance across compatible total extensions remain separate proof obligations.

**Theorem 1.1 (Nontrivial interventions precede their counterfactual outcomes).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/QueryImpliedCausalOrder.intervention_precedes_outcome`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/QueryImpliedCausalOrder.intervention_precedes_outcome` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The result unfolds one atom-level compiler obligation and applies the supplied query-order certificate.

**Theorem 1.2 (Reciprocal query-implied requirements are inconsistent).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/QueryImpliedCausalOrder.reciprocal_query_requirements_inconsistent`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/QueryImpliedCausalOrder.reciprocal_query_requirements_inconsistent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two opposed query requirements would force both directions of one strict order, contradicting asymmetry.

**Theorem 1.3 (Query obligations connect to the existing structural list order).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/QueryImpliedCausalOrder.query_requirement_has_structural_before`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/QueryImpliedCausalOrder.query_requirement_has_structural_before` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adapter reuses the canonical finite structural-model Before relation rather than introducing a second list-order semantics.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/QueryImpliedCausalOrder.intervention_precedes_outcome`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/QueryImpliedCausalOrder.query_requirement_has_structural_before`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/QueryImpliedCausalOrder.reciprocal_query_requirements_inconsistent`
- Dependency: [D5/S3/ConceptDynamics/Causal/StructuralEvaluationSemantics](../Causal/StructuralEvaluationSemantics.md)
