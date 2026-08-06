# Half-Density Unitarity

## Abstract

Half-density unitarity characterizes the critical line on a nontrivial ledger.

**Theorem 1.1 (Half-density unitarity characterizes the critical line).**

$$\forall x2 \in \mathrm{LedgerLength},\; \forall x3 \in \left(\exists x3 \in \mathord{\cdot},\; \mathit{x2}\left(\mathit{x3}\right) \ne 0\right),\; \forall x4 \in \mathrm{Complex},\; \left(\left(\forall x5 \in \mathord{\cdot},\; \mathrm{scalingLedger}\left(\mathit{x2}, \mathit{x4}, \mathit{x5}\right) = 0\right) \Leftrightarrow \left(\forall x5 \in \mathord{\cdot},\; \left\lVert \mathrm{halfDensityReading}\left(\mathit{x2}, \mathit{x4}, \mathit{x5}\right) \right\rVert = 1\right)\right) \land \left(\left(\forall x5 \in \mathord{\cdot},\; \left\lVert \mathrm{halfDensityReading}\left(\mathit{x2}, \mathit{x4}, \mathit{x5}\right) \right\rVert = 1\right) \Leftrightarrow \mathrm{re}\left(\mathit{x4}\right) = \mathrm{criticalAbscissa}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CriticalLine.unitarity_line_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an additive ledger with at least one nonzero length coordinate, every scaling entry vanishes exactly when every half-density-normalized reading has norm one, and both conditions hold exactly at real part one half. The nontriviality hypothesis replaces the source ledger's concrete prime-coordinate witness; the statement makes no claim about zeta zeros.

**Remark 1.2 (Unitary weight is not a zero proof).**

Lean statement: `D5/S3/Weil/CriticalLine.unitarity_line_iff`

*Formalization.* `D5/S3/Weil/CriticalLine.unitarity_line_iff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Half-density normalization singles out the critical line as the norm-preserving weight. It does not prove that a Mellin or Fourier cancellation occurs only at that weight, and spectral-dark-point interpretations remain external to this theorem.

## References

- Truth anchor: `D5/S3/Weil/CriticalLine.unitarity_line_iff`
- Dependency: [D5/S3/Weil/ReflectionLedger](ReflectionLedger.md)
