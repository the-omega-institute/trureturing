# Finite Transport-Certificate Clause Independence

## Abstract

Five constrained finite table models independently witness the necessity of the five canonical transport-certificate clauses.

**Definition 1.1 (Constrained finite transport model).**

$$FiniteTransportModel = (J, J', claim, version, receipt, premiseTable, transportTable,\\{}predictionTable, acceptanceTable, truthTable).$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.FiniteTransportModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The domain carrier has three points. Old and reported domains are Boolean characteristic tables; the receipt is exactly a content address, a domain table, and a version. Premises, transport assumptions, the partial prediction, acceptance, and claim truth are all finite Boolean tables. The structure contains no Prop-valued model field.

**Definition 1.2 (Five certificate coordinates).**

$$TransportCertificateClause = \{strictExpansion, receiptBound, conditionalTransport,\\{}totalOnNewOnly, refutingFailure\}.$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.TransportCertificateClause` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constructors follow the DECT 54.3 order: strict expansion, bound receipt, conditional transport, total prediction on the new-only domain, and a refuting failure witness.

**Definition 1.3 (Certificate derived from finite tables).**

$$\operatorname{finiteTransportCertificate}\left(M\right): TransportCert.$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.finiteTransportCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two proposition fields of the frozen certificate carrier are not free: they are equality-to-true readings of the one-entry finite tables. Its prediction is the model's finite partial-function table.

**Definition 1.4 (Semantic frame forced by finite tables).**

$$\operatorname{finiteTransportFrame}\left(M\right): TransportSemanticFrame.$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.finiteTransportFrame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Strict expansion and new-only membership are inherited from the frozen semantic frame and use characteristic-table membership.

Receipt matching is exact equality of address, domain, and version. Definedness is membership in the graph of the partial prediction. Failure means that an observed result is rejected. Claim truth and refutation share one truth table, with refutation exactly result disagreement at the same point.

**Definition 1.5 (Indexed canonical clause).**

$$\operatorname{finiteTransportClauseHolds}\left(M, C_j\right) = \operatorname{C}\left(C_j, M\right).$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.finiteTransportClauseHolds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each index selects one top-level conjunct of the existing legacy ValidTransportCert after applying the frozen toLegacy map. It does not define a second certificate-validity predicate.

**Definition 1.6 (Independent finite bad-report reading).**

$$\operatorname{finiteTransportBadReport}\left(M, C_j\right) = \operatorname{Bad}\left(C_j, M\right).$$

*Formalization.* `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.finiteTransportBadReport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The five cases read raw finite data: an old point lost by the report, a mismatched receipt field, true premises with a false reported-domain claim, an undefined new-only point, or only accepted or truth-aligned defined outputs. Badness is not defined as clause negation.

**Theorem 1.7 (All five transport-certificate clauses are independently necessary).**

$$\begin{gathered}(\forall M: FiniteTransportModel,\\{}(\forall C: TransportCertificateClause, \operatorname{finiteTransportClauseHolds}\left(M, C\right)) \iff \operatorname{ValidTransportCert}\left(\operatorname{finiteTransportFrame}\left(M\right).toLegacy, \operatorname{finiteTransportCertificate}\left(M\right), M.claim, M.oldDomain, M.reportedDomain, M.version\right))\\{}\land\\{}\forall C_j: TransportCertificateClause, \exists M_j: FiniteTransportModel,\\{}(\forall C_k: TransportCertificateClause, C_k \neq C_j \Rightarrow \operatorname{finiteTransportClauseHolds}\left(M_j, C_k\right)) \land\\{}\neg\operatorname{finiteTransportClauseHolds}\left(M_j, C_j\right) \land \operatorname{finiteTransportBadReport}\left(M_j, C_j\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.finite_transport_certificate_clause_independence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct checks clause fidelity: requiring every indexed coordinate is equivalent to the frozen canonical ValidTransportCert on every constrained finite model.

The second conjunct supplies five separate three-point models. For each omitted coordinate all four retained coordinates hold, the omitted coordinate fails, and the corresponding independently defined bad report is present. The totality countermodel uses two new-only points so that one can be undefined while the other carries the required refuting failure witness.

This closes OP4 from DECT part 55, atom generic-residual-38b77c703547818ccd62fb812de8f4084fc3f922b77676c15adff6a9624e1a0f, inside the constrained finite semantics class.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.FiniteTransportModel`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.TransportCertificateClause`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.finiteTransportBadReport`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.finiteTransportCertificate`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.finiteTransportClauseHolds`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.finiteTransportFrame`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence.finite_transport_certificate_clause_independence`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticTransportCertificateValidity](SemanticTransportCertificateValidity.md)
