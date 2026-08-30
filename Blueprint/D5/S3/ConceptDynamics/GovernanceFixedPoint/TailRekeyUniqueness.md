# Legal Tail Rekey Uniqueness

## Abstract

A legal tail rekey is uniquely determined by its document and ledger inputs.

**Theorem 1.1 (Legal tail rekeys are unique).**

$$\begin{aligned}\forall Id, Byte: \operatorname{Type},\\{}[DecidableEq(Id)],\\\forall tailEligible: Id \to Prop,\\\forall oldDocument, newDocument: List(Byte),\\\forall start: Nat,\\\forall oldEntry: LedgerEntry(Id, Byte),\\\forall active: ActiveIndex(Id, Byte),\\\forall settlement: Settlement(Id),\\\forall first, second: RekeyResult(Id, Byte),\\{}\\(LegalTailRekey(tailEligible, oldDocument, newDocument, start, oldEntry, active, settlement, first) \land\\{}\\LegalTailRekey(tailEligible, oldDocument, newDocument, start, oldEntry, active, settlement, second)) \Rightarrow \\first = second.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyUniqueness.legal_tail_rekey_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Legality fixes the predecessor, replacement entry, active-index update, and settlement view. Structure and function extensionality therefore identify any two legal results without a hash assumption.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyUniqueness.legal_tail_rekey_unique`
- Dependency: [D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyExistence](TailRekeyExistence.md)
