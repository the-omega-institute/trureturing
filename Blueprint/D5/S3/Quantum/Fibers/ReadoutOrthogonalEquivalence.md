# Trace Readout Fibers and Orthogonal Residuals

## Abstract

Finite trace readout fibers are centered-effect residual and projection fibers.

**Theorem 1.1 (Trace readout equality is orthogonal residual equality).**

$$\forall n, m, E: \operatorname{Fin}(m+1)\to\operatorname{Matrix}(n, n, \mathbb{C}), \rho, \sigma: \operatorname{Matrix}(n, n, \mathbb{C}), \operatorname{Density}(\rho)\land\operatorname{Density}(\sigma)\land\operatorname{EffectFamily}(E) \Rightarrow\\((q_{E}(\rho)=q_{E}(\sigma))\Leftrightarrow(\forall i, \operatorname{Tr}((\rho-\sigma)E_{i})=0))\land\\((\forall i, \operatorname{Tr}((\rho-\sigma)E_{i})=0)\Leftrightarrow(X_\rho-X_\sigma\in R_{0}))\land\\((X_\rho-X_\sigma\in R_{0})\Leftrightarrow(P_{V_{0}}(X_\rho)=P_{V_{0}}(X_\sigma))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/ReadoutOrthogonalEquivalence.readout_fiber_orthogonal_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state and effect objects are finite complex matrices. Density matrices are positive semidefinite and trace one, and every accessible effect and its complement are positive semidefinite. The readout is constructed from trace expectations.

Centering removes the scalar identity components from states and effects. Equality of readouts is equivalent to vanishing of every trace pairing, then to membership in the orthogonal complement of the centered-effect span, and finally to equality of the visible orthogonal projections.

The residual and projection equivalences are supplied directly by the canonical finite expectation-word theorem. Pinned library trace and matrix-inner-product declarations bridge that theorem to the source trace readout.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/ReadoutOrthogonalEquivalence.readout_fiber_orthogonal_equivalence`
- Dependency: [D5/S3/Quantum/Algebra/FutureWordOrthogonalResidual](../Algebra/FutureWordOrthogonalResidual.md)
- Dependency: [D5/S3/Quantum/Fibers/PhysicalFiber](PhysicalFiber.md)
