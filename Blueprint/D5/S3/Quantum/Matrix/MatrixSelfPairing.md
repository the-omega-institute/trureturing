# Matrix Self-Pairing

## Abstract

Positive trace-one matrix weights pair operations with themselves as nonnegative norm squares.

**Theorem 1.1 (Positive matrix self-pairings are nonnegative norm squares).**

$$\forall d,\ [\operatorname{Fintype}(d)],\ [\operatorname{DecidableEq}(d)],\ \forall \rho,x\in M_{d}(\mathbb{C}),\ \operatorname{PosSemidef}(\rho) \land \operatorname{Tr}(\rho)=1 \Rightarrow (\operatorname{Tr}(\rho x^{*} x)=\Vert x\sqrt{\rho}\Vert_{HS}^{2} \land 0\le\Vert x\sqrt{\rho}\Vert_{HS}^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/MatrixSelfPairing.matrix_self_pairing_and_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type d, positive semidefinite complex square matrix rho with trace one, and complex square matrix x, the trace of rho times x star times x equals the squared Frobenius norm of x times the positive continuous-functional-calculus square root of rho, and that real norm square is nonnegative. The displayed Hilbert-Schmidt notation denotes the Frobenius norm.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/MatrixSelfPairing.matrix_self_pairing_and_nonnegative`
- Dependency: [D5/S3/Quantum/GNSMatrix](../GNSMatrix.md)
