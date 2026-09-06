# Finite Linear Causal Identification

## Abstract

Finite response-type causal models compile layered assumptions and scalar queries to exact rational primal-dual certificates.

The compiler target is a finite exact rational system. Response-type masses are primal variables, observational or interventional information supplies data rows, causal structure supplies structural rows, and optional sensitivity knowledge supplies separately labeled rows.

Equalities can be represented by paired inequalities and probability nonnegativity by explicit rows. The query is a rational linear functional of the response-type mass vector.

The semantic layer delegates arithmetic soundness to the generic linear objective certificate library. Matching rational dual and primal witnesses certify exact lower and upper causal endpoints without trusting the optimizer that discovered them.

**Theorem 1.1 (A generic rational lower certificate proves the compiled causal bound).**

Lean statement: `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.query_lower_bound_of_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.query_lower_bound_of_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every feasible response-type mass vector satisfies the bound after exact replay of the nonnegative row combination.

**Theorem 1.2 (A generic rational upper certificate proves the compiled causal bound).**

Lean statement: `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.query_upper_bound_of_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.query_upper_bound_of_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The certificate checker is independent of whether a row originated from data, causal structure, or a sensitivity assumption.

**Theorem 1.3 (A complete rational primal-dual payload certifies both exact causal endpoints).**

Lean statement: `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.exact_endpoints_of_primal_dual_payload`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.exact_endpoints_of_primal_dual_payload` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two valid dual certificates and two attaining feasible response distributions close the endpoint-optimality proof obligations for a finite linear causal query.

**Theorem 1.4 (Every compiled row retains an auditable semantic provenance).**

Lean statement: `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.constraint_layer_is_exhaustive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.constraint_layer_is_exhaustive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The layer tag makes explicit whether tightening comes from identified data, structural causal restrictions, or external sensitivity knowledge.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.constraint_layer_is_exhaustive`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.exact_endpoints_of_primal_dual_payload`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.query_lower_bound_of_certificate`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification.query_upper_bound_of_certificate`
- Dependency: [D5/S0/Certificates/LinearObjectiveDual](../../../S0/Certificates/LinearObjectiveDual.md)
