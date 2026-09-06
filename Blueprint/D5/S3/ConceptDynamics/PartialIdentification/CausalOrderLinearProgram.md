# Causal-Order Linear Programs

## Abstract

Canonical response-signature events compile to exact finite causal linear programs whose rational certificates bound the original SCM event probability.

Layered observational, structural, and sensitivity constraints act on a finite response-signature mass vector. A Boolean counterfactual event supplies the objective indicator row.

The compiled query equals the signature event mass exactly. Existing rational lower and upper dual certificates therefore prove bounds on the causal event itself.

An exogenous structural model maps each latent state to one deterministic signature. Pushing its mass through this map preserves every Boolean event probability, giving the semantic bridge from an SCM witness to the LP variables.

**Theorem 1.1 (The compiled objective equals the signature event probability).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.signatureEventProblem_query_eq`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.signatureEventProblem_query_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiler selects the event indicator as its objective coefficient, so equality follows from the response-signature linearity theorem.

**Theorem 1.2 (A rational dual certificate bounds the causal event probability).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.signature_event_upper_bound_of_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.signature_event_upper_bound_of_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replaying the generic finite causal upper certificate and transporting across the objective equality yields the event bound.

**Theorem 1.3 (Exogenous and response-signature event evaluations agree).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.signature_event_mass_pushforward`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.signature_event_mass_pushforward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite sum exchange and deterministic signature assignment show that evaluating the event before or after pushforward gives the same probability.

**Theorem 1.4 (Every finite signature-law witness has an exogenous realization).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.identity_exogenous_realizes_signature_event`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.identity_exogenous_realizes_signature_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The response-signature carrier itself serves as the latent state space, making the structural realization explicit at the law level.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.identity_exogenous_realizes_signature_event`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.signatureEventProblem_query_eq`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.signature_event_mass_pushforward`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram.signature_event_upper_bound_of_certificate`
- Dependency: [D5/S3/ConceptDynamics/Causal/FiniteLinearCausalIdentification](../Causal/FiniteLinearCausalIdentification.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/CanonicalResponseSignature](CanonicalResponseSignature.md)
