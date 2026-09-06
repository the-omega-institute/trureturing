# Canonical Causal Response Signatures

## Abstract

A finite total causal order yields finite predecessor-indexed deterministic response signatures whose event probabilities are exact linear objectives.

A total order assigns every endogenous coordinate a unique position. At position j, a canonical response table maps assignments to the j predecessor positions into the current variable's value.

For finite value spaces, the dependent product of all such response tables is finite. Its probability masses therefore form a finite response-type vector.

Every Boolean observational or counterfactual event on signatures has an indicator coefficient. Summing those coefficients against signature masses is exactly a rational linear objective. Pushing a finite exogenous law through its deterministic signature map preserves total mass and event probabilities.

**Theorem 1.1 (Every node occupies a unique total-order position).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature.node_has_unique_position`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature.node_has_unique_position` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse permutation gives the position witness, and injectivity gives uniqueness.

**Theorem 1.2 (A signature event probability is an exact linear objective).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature.signature_event_mass_eq_linearObjective`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature.signature_event_mass_eq_linearObjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The event indicator is zero or one on each response signature, so the finite event sum coincides term by term with linear-objective evaluation.

**Theorem 1.3 (Every signature mass has an identity exogenous realization).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature.pushforwardSignatureMass_id`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature.pushforwardSignatureMass_id` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the signature carrier itself as the exogenous state space and the identity as the signature map reproduces every mass exactly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature.node_has_unique_position`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature.pushforwardSignatureMass_id`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature.signature_event_mass_eq_linearObjective`
- Dependency: [D5/S0/Certificates/LinearObjectiveDual](../../../S0/Certificates/LinearObjectiveDual.md)
