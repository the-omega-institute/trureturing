# Semantic Entries Reopen at the Next Layer

## Abstract

A traceable semantic entry shifts losslessly to an open entry at the next layer.

**Theorem 1.1 (The semantic layer shift is bijective).**

$$\operatorname{Bijective}(semanticLayerShiftEquiv)$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/SemanticLayerShift.semantic_layer_shift_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A current-layer ledger entry whose detector has a semantic type mismatch is shifted into an open entry at the next layer. Source, detector, and future-budget types are connected by explicit equivalences, while the status transposition exchanges semantic and open and leaves closed and tail fixed. Restricting this full ledger equivalence to the two status fibers gives the typed layer shift. Bijectivity records the source atom's traceability demand: no entry is lost and no duplicate is introduced during reopening.

Pinned Mathlib was searched before implementation. It provides Equiv.swap for the status transposition, Equiv.subtypeEquiv for restricting an equivalence to matching predicates, and Equiv.bijective for the final theorem. It has no declaration for this ledger-specific semantic-to-open transition, so the Lean module constructs only that local equivalence and delegates its bijectivity to Mathlib. The claim is structural and carries no numerical certificate.

## References

- Truth anchor: `D5/S0/Computability/SemanticLayerShift.semantic_layer_shift_bijective`
- Dependency: [D5/S0/History/ResidualLedger](../History/ResidualLedger.md)
