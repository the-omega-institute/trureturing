# Referenced Reversal Events

## Abstract

Integer ledgers admit exact, explicitly referenced reversal events.

**Theorem 1.1 (Group-ledger reversals cancel and record every negative coordinate).**

$$\operatorname{Bijective}(code) \land \forall u, code(-u)=delta(rev(u)) \land code(u)+delta(rev(u))=0 \land \operatorname{supp}(delta(rev(u)))=\operatorname{supp}(code(u)) \land \forall a, refs(rev(u),a)\neq\emptyset \Leftrightarrow delta(rev(u))(a)<0$$

*Proof.* Machine-checked in Lean as `D5/S0/History/ReferencedReversal.group_ledger_reversal_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The group-completed ledger on any address type is represented by finitely supported integer coordinates. Given a reference for each address, reversal negates every coordinate. The reversed entry cancels the original exactly and has the same finite support, while its reference set is nonempty exactly where the reversal coordinate is negative. Thus a negative entry cannot occur without an explicit reference to the item being reversed.

The library was searched before proving. Pinned Mathlib already identifies the free abelian group on an address type with its finitely supported integer-valued functions through `FreeAbelianGroup.equivFinsupp`, and supplies support preservation under negation through `Finsupp.support_neg`. The Lean theorem is a thin wrapper around that algebraic core plus the repository's small referenced-event structure. Mathlib contains no event type that requires audit references on negative coordinates; that field is the source atom's additional content.

## References

- Truth anchor: `D5/S0/History/ReferencedReversal.group_ledger_reversal_spec`
