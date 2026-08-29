# Semantic Transport-Certificate Validity

## Abstract

Typed transport-certificate validity is exactly its legacy propositional image.

**Theorem 1.1 (Typed and legacy transport-certificate validity are equivalent).**

$$\begin{gathered}\forall S, cert, claim, J, J', version,\\{}\operatorname{ValidSemanticTransportCert}\left(S, cert, claim, J, J', version\right) \iff\\{}\operatorname{ValidTransportCert}\left(S.toLegacy, cert, claim, J, J', version\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticTransportCertificateValidity.valid_semantic_transport_cert_iff_valid_transport_cert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The typed certificate names strict expansion, a claim-bound source receipt, conditional transport, total prediction coverage on the new-only domain, and a result-bearing refuting failure.

The forward implication forgets only the stored run result. In the reverse implication, failure and refutation initially expose two existential results; both are outputs of the same partial run at the same point, so injectivity of Option.some identifies them without decidable equality or a result-uniqueness axiom.

This discharges obligation 57.3-C from definition-escape-completion-theory atom generic-residual-52c9a2ebbc45db7def84de526f0e46314b1acd696edde2615911dddda21aa70f.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticTransportCertificateValidity.valid_semantic_transport_cert_iff_valid_transport_cert`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeSemantics/TransportRefutationProjection](TransportRefutationProjection.md)
