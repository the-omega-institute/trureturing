# Incomparable Repair Costs

## Abstract

A finite two-repair cost face has two distinct Pareto-minimal incomparable receipts.

**Theorem 1.1 (Incomparable repairs have no unique cost choice).**

$$tradeReceipt(true) \in tradeFace \land tradeReceipt(false) \in tradeFace \land tradeReceipt(true) \neq tradeReceipt(false) \land \neg(tradeReceipt(true) \le tradeReceipt(false)) \land \neg(tradeReceipt(false) \le tradeReceipt(true)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/IncomparableRepairCosts.incomparable_repairs_no_unique_choice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Bool witness represents two repairs. Their imported tax receipts are distinct minimal elements of the same valid cost face, while neither receipt is componentwise below the other.

Thus the formal cost order exposes a Pareto tradeoff: one repair improves one coordinate while the other improves the opposing coordinate. No unique choice follows from this order alone; an external priority rule would be additional structure.

The Lean declaration is a direct wrapper around the existing frozen theorem `PriceFaceOrder.trade_face_two_incomparable_minima`; no ethical predicate or domain-specific responsibility notion is encoded.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/IncomparableRepairCosts.incomparable_repairs_no_unique_choice`
- Dependency: [D5/S3/ResourceOrder/PriceFaceOrder](../../ResourceOrder/PriceFaceOrder.md)
