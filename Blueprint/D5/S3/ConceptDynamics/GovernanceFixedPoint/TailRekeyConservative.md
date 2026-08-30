# Legal Tail Rekey Conservativity

## Abstract

Every legal tail rekey preserves settlement and changes only its active source.

**Theorem 1.1 (Legal tail rekeys are conservative).**

$$\begin{aligned}\forall Id, Byte: \operatorname{Type},\\{}[DecidableEq(Id)],\\\forall tailEligible: Id \to Prop,\\\forall oldDocument, newDocument: List(Byte),\\\forall start: Nat,\\\forall oldEntry: LedgerEntry(Id, Byte),\\\forall active: ActiveIndex(Id, Byte),\\\forall settlement: Settlement(Id),\\\forall result: RekeyResult(Id, Byte),\\{}\\LegalTailRekey(tailEligible, oldDocument, newDocument, start, oldEntry, active, settlement, result) \Rightarrow\\{}ConservativeRekey(active, settlement, oldEntry, result).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyConservative.legal_tail_rekey_is_conservative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named conservativity predicate records the old predecessor and stable logical identifier, equality of the complete settlement view, the unique active key at the target identifier, and preservation of every other identifier's active key.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyConservative.legal_tail_rekey_is_conservative`
- Dependency: [D5/S3/ConceptDynamics/GovernanceFixedPoint/TailRekeyExistence](TailRekeyExistence.md)
