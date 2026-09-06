# Attaining Canonical Structural Models

## Abstract

Every finite canonical response-signature probability law is realized by a structural model whose shared exogenous state indexes that complete signature.

A canonical ordered structural model has one finite exogenous carrier. Each exogenous state selects a complete deterministic response signature, and each structural equation reads the response table stored at the corresponding total-order position.

Given any normalized nonnegative signature law, the signature carrier itself can serve as the exogenous state space. The identity signature map then reproduces the nominated law exactly.

This construction is the primal tightness bridge. A feasible LP mass vector is converted into a finite structural witness attaining the same Boolean counterfactual event probability.

**Theorem 1.1 (The canonical structural witness realizes the nominated signature law).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/AttainingStructuralModel.canonicalSCM_inducedSignatureMass`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/AttainingStructuralModel.canonicalSCM_inducedSignatureMass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Identity pushforward on the signature carrier returns every mass coordinate unchanged.

**Theorem 1.2 (Canonical equations are exactly the stored response tables).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/AttainingStructuralModel.canonicalSCM_structuralResponse`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/AttainingStructuralModel.canonicalSCM_structuralResponse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every total-order position and exogenous signature state, the structural response is definitionally the selected predecessor-response table.

**Theorem 1.3 (The structural witness attains the LP event probability).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/AttainingStructuralModel.canonicalSCM_attains_signature_event`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/AttainingStructuralModel.canonicalSCM_attains_signature_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating a Boolean event on the canonical exogenous states gives the same finite sum as evaluating it on the signature-law vector.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/AttainingStructuralModel.canonicalSCM_attains_signature_event`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/AttainingStructuralModel.canonicalSCM_inducedSignatureMass`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/AttainingStructuralModel.canonicalSCM_structuralResponse`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/CausalOrderLinearProgram](CausalOrderLinearProgram.md)
