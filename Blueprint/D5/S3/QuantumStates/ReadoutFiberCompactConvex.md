# Compact Convex Readout Fibers

## Abstract

Every nonempty finite-dimensional positive readout fiber is compact and convex.

**Theorem 1.1 (Nonempty positive readout fibers are compact and convex).**

$$\forall n, k, [\operatorname{Fintype}(n)], [\operatorname{Nonempty}(n)], [\operatorname{Finite}(k)],\ readout: \operatorname{LinearMap}_{\mathbb{C}}(\operatorname{Matrix}(n, n, \mathbb{C}) \to k \to \mathbb{C}), y: k \to \mathbb{C},\ \operatorname{Nonempty}(\operatorname{readoutFiber}(readout, y)) \Rightarrow \operatorname{IsCompact}(\operatorname{readoutFiber}(readout, y)) \land \operatorname{Convex}(\mathbb{R}, \operatorname{readoutFiber}(readout, y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/ReadoutFiberCompactConvex.readout_fiber_compact_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fiber is built from the source primitives: a finite-dimensional complex matrix state, a linear readout, positivity, and trace-one normalization. A nonempty fiber has a witness state, so its arbitrary readout value agrees with the frozen physical-fiber construction.

The compactness and convexity clauses are discharged by the existing repository theorem D5/S3/Quantum/Fibers/PhysicalFiber. The new statement only transports that theorem from a witness readout value to an arbitrary nonempty fiber.

## References

- Truth anchor: `D5/S3/QuantumStates/ReadoutFiberCompactConvex.readout_fiber_compact_convex`
- Dependency: [D5/S3/Quantum/Fibers/PhysicalFiber](../Quantum/Fibers/PhysicalFiber.md)
