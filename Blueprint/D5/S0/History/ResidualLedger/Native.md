# The native residual ledger representation

## Abstract

A residual ledger entry is equivalent to the tuple of its four fields.

**Definition 1.1 (Recovering an entry from its components).**

$$ResidualLedgerEntry \sim Source \times Detector \times ResidualStatus \times NextAction$$

*Formalization.* `D5/S0/History/ResidualLedger/Native.residualLedgerEquivComponents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map reads the source, detector, status and next action in field order. The inverse builds a record from the same four components. Pattern matching on the record and tuple proves both round trips.

## References

- Truth anchor: `D5/S0/History/ResidualLedger/Native.residualLedgerEquivComponents`
