# The Residual Ledger

## Abstract

A residual ledger entry consists exactly of its source, detector, four-state status, and next action.

**Theorem 1.1 (Residual ledger entries are losslessly determined by four components).**

$$\operatorname{ResidualLedgerEntry} \sim Source \times Detector \times \operatorname{ResidualStatus} \times NextAction$$

*Proof.* Machine-checked in Lean as `D5/S0/History/ResidualLedger.residual_ledger_components_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A residual ledger entry is a typed workflow object with four fields. The source records where the discrepancy arose, the detector records the readout that exposes it, the status is one of open, closed, tail, or semantic, and the next-action field stores its future treatment or budget. The Lean carrier makes those alternatives explicit and prevents an entry from silently occupying an unnamed fifth state.

The theorem packages the definition as a lossless equivalence between the named record and the product of its four components. The library was searched before proving: pinned Mathlib supplies standard product equivalences and `Equiv.bijective`, but no residual-ledger workflow type. The implementation therefore adds only the source-specific record and uses Mathlib's bijectivity theorem for the final claim. The source atom contains no numerical certificate.

## References

- Truth anchor: `D5/S0/History/ResidualLedger.residual_ledger_components_bijective`
