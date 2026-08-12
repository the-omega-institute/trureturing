# Matrix-State Cone Sections

## Abstract

The positivity and normalization clauses of a finite matrix state are sections of its GNS norm-square identity.

**Theorem 1.1 (Matrix-state positivity and normalization are GNS cone sections).**

$$\forall d,\ [\operatorname{Fintype}(d)],\ [\operatorname{DecidableEq}(d)],\ \forall \rho\in M_{d}(\mathbb{C}),\ \operatorname{PosSemidef}(\rho) \land \operatorname{Tr}(\rho)=1 \Rightarrow [\\\left(\forall x\in M_{d}(\mathbb{C}),\ \operatorname{Tr}(\rho x^{*} x)=\Vert x\sqrt{\rho}\Vert_{HS}^{2} \land 0 \leq \operatorname{Tr}(\rho x^{*} x)\right) \land\\\operatorname{Tr}(\rho 1^{*} 1)=1 \land\\\Vert\sqrt{\rho}\Vert_{HS}^{2}=\operatorname{Tr}(\rho) \land\\\operatorname{Tr}(\rho)=1\\]$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/GNSStateCone.state_cone_sections` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be a finite index type and rho a positive semidefinite complex d-by-d matrix with trace one. For every complex matrix x, the trace expectation of x star x is exactly the squared Frobenius norm of x times the positive continuous-functional-calculus square root of rho, and is therefore nonnegative.

Specializing x to the identity gives normalized expectation one. The same specialization identifies the squared Frobenius norm of the square root of rho with the trace of rho, which is one. Thus the two state-space clauses are the positivity and identity sections of the same squared-length formula.

The declaration reuses the matrix GNS identity rather than proving it again. Its scope is finite-dimensional complex matrix algebras; it makes no claim for arbitrary C-star algebras.

## References

- Truth anchor: `D5/S3/QuantumStates/GNSStateCone.state_cone_sections`
- Dependency: [D5/S3/Quantum/GNSMatrix](../Quantum/GNSMatrix.md)
