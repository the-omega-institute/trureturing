# Legal Ledger Fixed Set

## Abstract

Fixed membership of legal proof ledgers under witness-preserving extensions.

Let P, Proof, Ax and Model be arbitrary types, and let k be kernel data. The kernel accepts or rejects each proof of a proposition and reads its finite sets of axioms and direct references. Proved means that an accepted proof uses only permitted axioms.

A certified core has finitely many nodes, an exact witness for each node, accepted witnesses using permitted axioms, closure under their actual references, and an acyclic reference relation. A certificate for a proposition is such a core containing it. A legal ledger adds an arbitrary registered frontier disjoint from its core; the frontier need not be finite.

An extension retains every old node, every derived edge, and the exact old witness. A transformation is a total map on all legal ledgers, and it is admissible when it is an extension on every input. Fix consists of propositions whose frozen membership is invariant under every such admissible map.

**Theorem 1.1 (A certificate gives an admissible total transformation).**

$$\forall p: P, \forall C: \operatorname{Certificate}\left(k, p\right), \operatorname{Admissible}\left(\operatorname{addWithCertificate}\left(p, C\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/LegalLedgerFixedSet.addWithCertificate_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transformation is the identity when the proposition is already frozen. Otherwise it takes the finite union of the old core and the certificate, keeps old witnesses on every overlap, and uses certificate witnesses only for new nodes. It removes certificate nodes from the frontier.

Old nodes reference only old nodes. Edges between new nodes are certificate edges. Tagging old and new nodes by the two sides of a lexicographic sum maps each selected-witness edge into an irreflexive transitive relation. The transitive-closure lifting theorem rules out cycles. Acceptance, axiom permission and reference closure follow from whichever witness was selected, without an overlap compatibility premise.

The resulting ledger is legal for every legal input and retains all old nodes, edges and witnesses.

**Theorem 1.2 (Fixed membership is frozen or unprovable membership).**

$$\forall laws: \operatorname{SourceLaws}\left(k\right), \forall L: \operatorname{LegalLedger}\left(k\right), \operatorname{Fix}\left(L\right) = \operatorname{Frozen}\left(L\right) \cup \{p: P \mid \neg \operatorname{Proved}\left(k, p\right)\}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/LegalLedgerFixedSet.fixed_eq_frozen_union_unprovable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SourceLaws includes kernel soundness in every permitted-axiom model, certificate existence for every proved proposition, and consistency: a proposition and its negation cannot both be proved. All three remain explicit in the theorem contract. The structural argument uses the certificate-existence conjunct.

Frozen propositions stay frozen by admissibility. An unprovable proposition cannot appear in any legal core, since its selected witness would prove it. Hence both kinds have invariant membership.

Conversely, an unfrozen proved proposition has a certificate. The admissible certificate transformation makes it frozen, contradicting invariance. This argument quantifies over all legal ledgers and all total admissible transformations; it makes no claim about record ledgers or transformations that permit invalid witnesses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/LegalLedgerFixedSet.addWithCertificate_admissible`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/LegalLedgerFixedSet.fixed_eq_frozen_union_unprovable`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder](DependencyReachabilityOrder.md)
