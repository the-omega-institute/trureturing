# Zero Norm Propagation for Matrix States

## Abstract

A positive normalized matrix trace functional propagates a zero quadratic value to every mixed value.

**Theorem 1.1 (The mixed trace is a Gram pairing after multiplication by the square root).**

$$\forall d \in \operatorname{Type},\; [\operatorname{Fintype}\left(d\right)][\operatorname{DecidableEq}\left(d\right)]\forall rho \in \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\; \forall h \in \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\; \forall g \in \operatorname{Matrix}\left(d, d, \mathbb{C}\right),\; \operatorname{Matrix.PosSemidef}\left(rho\right) \Rightarrow \operatorname{D5.S3.QuantumStates.GNSZeroPropagation.stateFunctional}\left(rho, \operatorname{Matrix.conjTranspose}\left(h\right) \cdot g\right) = \operatorname{Matrix.trace}\left(\operatorname{Matrix.conjTranspose}\left(h \cdot \operatorname{CFC.sqrt}\left(rho\right)\right) \cdot g \cdot \operatorname{CFC.sqrt}\left(rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/GNSZeroPropagation.cross_trace_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive semidefinite matrix rho and arbitrary matrices h and g, the trace pairing of rho with the conjugate transpose of h times g equals the Gram trace of h times the positive square root of rho and g times that square root.

**Theorem 1.2 (A zero quadratic value annihilates every mixed value).**

$$\forall d,\ [\operatorname{Fintype}(d)],\ [\operatorname{DecidableEq}(d)],\ \forall \rho, g \in \operatorname{Matrix}(d, d, \mathbb, {C}),\ \operatorname{PosSemidef}(\rho) \land \operatorname{trace}(\rho) = 1 \land \operatorname{stateFunctional}(\rho, g^{*} g) = 0 \Rightarrow \forall h \in \operatorname{Matrix}(d, d, \mathbb, {C}),\ \operatorname{stateFunctional}(\rho, h^{*} g) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/GNSZeroPropagation.gns_zero_norm_propagation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state functional is the source trace pairing Tr(rho times a), with rho positive semidefinite and trace one. Its quadratic value at g is the squared Frobenius norm of g times the positive square root of rho.

A zero quadratic value therefore makes g times the square root of rho equal to zero. The same factorization for an arbitrary h proves the mixed trace value Tr(rho h star g) is zero.

The matrix GNS identity is reused directly; the deposited statement retains positivity, normalization, and the universal mixed-value conclusion as public clauses.

## References

- Truth anchor: `D5/S3/QuantumStates/GNSZeroPropagation.cross_trace_factorization`
- Truth anchor: `D5/S3/QuantumStates/GNSZeroPropagation.gns_zero_norm_propagation`
- Dependency: [D5/S3/Quantum/GNSMatrix](../Quantum/GNSMatrix.md)
