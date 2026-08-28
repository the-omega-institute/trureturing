# Trace-Zero Hermitian Readout Fibers

## Abstract

Real trace-zero Hermitian readout fibers equal residual and projection fibers.

**Theorem 1.1 (Trace readout fibers are residual and projection fibers on the real carrier).**

$$\forall d: \operatorname{Type}, m: Nat, [\operatorname{Fintype}(d)], [\operatorname{Nonempty}(d)], [\operatorname{DecidableEq}(d)]\\{}E: \operatorname{Fin}(m+1) \to \operatorname{Matrix}(d, d, \mathbb{C}), \rho, \sigma: \operatorname{Matrix}(d, d, \mathbb{C}), \rho \operatorname{PosSemidef} \land \operatorname{trace}(\rho) = 1, \sigma \operatorname{PosSemidef} \land \operatorname{trace}(\sigma) = 1,\\{}\forall i: \operatorname{Fin}(m+1), (E(i) \operatorname{PosSemidef} \land (1 - E(i)) \operatorname{PosSemidef}) \Rightarrow\\{}V = \operatorname{HermitianTraceZero}(d), \operatorname{V0}(V, E) = \operatorname{span}_{\mathbb{R}}(\operatorname{range}(\operatorname{centeredEffect}(E(i)))), \operatorname{R0}(V, E) = V0^{\perp},\\{}((\operatorname{finiteTraceReadout}(E, \rho)=\operatorname{finiteTraceReadout}(E, \sigma)) \Leftrightarrow (\forall i, \operatorname{Tr}((\rho-\sigma)E(i)) = 0)) \land\\{}((\forall i, \operatorname{Tr}((\rho-\sigma)E(i)) = 0) \Leftrightarrow (X_\rho - X_\sigma \in R_{0})) \land\\{}((X_\rho - X_\sigma \in R_{0}) \Leftrightarrow (P_{V_{0}}(X_\rho)=P_{V_{0}}(X_\sigma))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence.readout_fiber_orthogonal_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public carrier is the real subspace HermitianTraceZero(d) of complex d by d matrices that are Hermitian and trace zero. Raw effects and density matrices retain their source positivity and trace-one predicates; centered effects and centered states are constructed in this carrier.

Let V_0 be the real span of the centered effects and R_0 its orthogonal complement in HermitianTraceZero(d). Equality of the finite trace readouts is equivalent to every trace pairing being zero, to the centered-state difference lying in R_0, and to equal orthogonal projections onto V_0.

The frozen finite expectation-word residual theorem is applied on the real subtype. Matrix trace and complex-inner-product identities bridge its real pairing to the source's complex trace equation.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence.readout_fiber_orthogonal_equivalence`
- Dependency: [D5/S3/Quantum/Fibers/ReadoutOrthogonalEquivalence](ReadoutOrthogonalEquivalence.md)
