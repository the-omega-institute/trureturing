# Record Channel Fixed Point

## Abstract

A record channel fixes exactly the matrices satisfying its entrywise Gram equations.

**Theorem 1.1 (Record-channel fixed points are entrywise Gram equations).**

$$\forall d, e: Nat, record: Fin \to Fin \to Complex, rho: Matrix(Fin(d), Fin(d), Complex), recordChannel(record, rho) = rho \iff \forall i, j: Fin(d), (recordGram(record, i, j) - 1) \times rho(i)(j) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FixedAlgebra/RecordChannelFixedPoint.record_channel_fixed_iff_entry_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The record Gram matrix and channel are the canonical source-constructed primitives. Comparing matrix entries turns channel equality into the displayed product equation, and the converse reconstructs the channel entry by entry.

## References

- Truth anchor: `D5/S3/Quantum/FixedAlgebra/RecordChannelFixedPoint.record_channel_fixed_iff_entry_equations`
- Dependency: [D5/S3/Quantum/FixedAlgebra/SingletonRecordClassicality](SingletonRecordClassicality.md)
