# Legal Tail Rekey Existence

## Abstract

Every eligible active tail has a legal rekey along a document prefix extension.

**Theorem 1.1 (Legal tail rekeys exist).**

$$\begin{aligned}\forall Id, Byte: \operatorname{Type},\\{}[DecidableEq(Id)],\\\forall tailEligible: Id \to Prop,\\\forall oldDocument, newDocument: List(Byte),\\\forall start: Nat,\\\forall oldEntry: LedgerEntry(Id, Byte),\\\forall active: ActiveIndex(Id, Byte),\\\forall settlement: Settlement(Id),\\tailEligible(oldEntry.logicalId) \land PrefixExtension(oldDocument, newDocument) \land \\start \le oldDocument.length \land oldEntry.bytes = TailBytes(oldDocument, start) \land \\ActiveSource(active, oldEntry.logicalId, oldEntry.key) \Rightarrow \\\exists result: RekeyResult(Id, Byte), LegalTailRekey(tailEligible, oldDocument, newDocument, start, oldEntry, active, settlement, result).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyExistence.legal_tail_rekey_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The replacement keeps the logical identifier and settlement, records the old content key as predecessor, and updates only the active key selected by that identifier.

The document prefix extension supplies the replacement tail's prefix clause through the tail-span preservation theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyExistence.legal_tail_rekey_exists`
- Dependency: [D5/S3/ConceptDynamics/GovernanceFixedPoint/TailSpanPrefixExtension](TailSpanPrefixExtension.md)
