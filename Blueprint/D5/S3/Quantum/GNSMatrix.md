# Matrix GNS Identity

## Abstract

Positive trace-one matrix weights are Hilbert-Schmidt norm squares.

**Theorem 1.1 (Positive matrix weights are Hilbert-Schmidt norm squares).**

$$\forall d,\ [\operatorname{Fintype}(d)],\ [\operatorname{DecidableEq}(d)],\ \forall \rho,x\in M_{d}(\mathbb{C}),\ \operatorname{PosSemidef}(\rho) \land \operatorname{Tr}(\rho)=1 \Rightarrow \operatorname{Tr}(\rho x^{*} x)=\Vert x\sqrt{\rho}\Vert_{HS}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GNSMatrix.gns_matrix_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type d, positive semidefinite complex square matrix rho with trace one, and complex square matrix x, the trace of rho times x star times x equals the squared Frobenius norm of x times the positive continuous-functional-calculus square root of rho. The displayed Hilbert-Schmidt notation denotes that Frobenius norm.

## References

- Truth anchor: `D5/S3/Quantum/GNSMatrix.gns_matrix_identity`
