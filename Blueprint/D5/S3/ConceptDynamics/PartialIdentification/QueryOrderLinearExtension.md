# Query-Implied Causal-Order Linear Extensions

## Abstract

Certified counterfactual precedence constraints admit a complete linear extension that preserves every nontrivial query obligation.

A counterfactual query first emits intervention-to-outcome precedence constraints. A partial-order certificate records that these obligations are jointly acyclic and embeds them in one causal order relation.

The Szpilrajn extension theorem completes that relation without deleting any certified edge. Every emitted requirement survives in the extension, while its intervention and outcome coordinates remain distinct.

This result supplies an indexing order for canonical response signatures. It leaves LP soundness and invariance across alternative compatible extensions as separate theorem obligations.

**Theorem 1.1 (Query-generated precedence requirements are nontrivial).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/QueryOrderLinearExtension.query_requirement_source_ne_target`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/QueryOrderLinearExtension.query_requirement_source_ne_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source coordinate belongs to the intervention set and is explicitly distinct from the atom's outcome, which is the target coordinate.

**Theorem 1.2 (Every certified query partial order has a preserving linear extension).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/QueryOrderLinearExtension.query_partial_order_has_linear_extension`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/QueryOrderLinearExtension.query_partial_order_has_linear_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness relation is linear, extends the full certified partial order, and preserves each query-generated intervention-to-outcome requirement together with source-target disequality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/QueryOrderLinearExtension.query_partial_order_has_linear_extension`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/QueryOrderLinearExtension.query_requirement_source_ne_target`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/QueryImpliedCausalOrder](QueryImpliedCausalOrder.md)
