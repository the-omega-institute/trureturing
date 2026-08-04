# Half-Density Unitarity

## Abstract

Half-density unitarity characterizes the critical line on a nontrivial ledger.

<a id="describe-half-density-unitarity-characterizes-the-critical-line"></a>

**Theorem 1.1 (Half-density unitarity characterizes the critical line).**

$$\forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ (\exists a,\ell(a)\neq 0) \Rightarrow \forall s\in\mathbb{C},\ ((\forall a,\operatorname{scalingLedger}(\ell,s,a)=0) \Leftrightarrow (\forall a,\Vert\operatorname{halfDensityReading}(\ell,s,a)\Vert=1)) \land ((\forall a,\Vert\operatorname{halfDensityReading}(\ell,s,a)\Vert=1) \Leftrightarrow \Re(s)=\frac{1}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CriticalLine.unitarity_line_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an additive ledger with at least one nonzero length coordinate, every scaling entry vanishes exactly when every half-density-normalized reading has norm one, and both conditions hold exactly at real part one half. The nontriviality hypothesis replaces the source ledger's concrete prime-coordinate witness; the statement makes no claim about zeta zeros.

<a id="describe-unitary-weight-is-not-a-zero-proof"></a>

**Remark 1.2 (Unitary weight is not a zero proof).**

Lean statement: `D5/S3/Weil/CriticalLine.unitarity_line_iff`

*Formalization.* `D5/S3/Weil/CriticalLine.unitarity_line_iff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Half-density normalization singles out the critical line as the norm-preserving weight. It does not prove that a Mellin or Fourier cancellation occurs only at that weight, and spectral-dark-point interpretations remain external to this theorem.

## References

- Truth anchor: `D5/S3/Weil/CriticalLine.unitarity_line_iff`
