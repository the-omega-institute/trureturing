# Typed Transport-Refutation Projection

## Abstract

A typed transport refutation witness exposes its same-run propositional consequences.

**Theorem 1.1 (A typed refutation witness projects to four propositions).**

$$\forall w : \operatorname{TransportRefutationWitness}\left(S, cert, claim, J, J'\right), \exists z, \operatorname{SemanticNewOnly}\left(S, z, J, J'\right) \land\\{}(\operatorname{SemanticPredictionDefined}\left(S, cert.falsifiablePrediction, z\right)) \land\\{}(\operatorname{SemanticPredictionFails}\left(S, cert.falsifiablePrediction, z\right)) \land\\{}(\operatorname{SemanticRefutes}\left(S, z, cert, claim\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/TransportRefutationProjection.transport_refutation_witness_projects_to_prop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The semantic frame interprets the prediction registered by the frozen transport-certificate carrier. The witness stores one point, one returned result, failure of that result, and refutation of the same claim by the same result.

The conclusion exposes new-domain membership, prediction definedness, prediction failure, and claim refutation at that one point. Each run-dependent conjunct is constructed from the witness's stored result; no result equality or decidability assumption is used.

This discharges obligation 57.3-B from definition-escape-completion-theory atom generic-residual-ec58c77abc2d1b2b22f690f3a3d268dcc2ff353d26dd2f317c0da0845820b8e0.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/TransportRefutationProjection.transport_refutation_witness_projects_to_prop`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticStrictSubsetWitness](SemanticStrictSubsetWitness.md)
- Dependency: [D5/S3/ConceptDynamics/Transport/TransportCertificateValidity](../Transport/TransportCertificateValidity.md)
