# Finite-Dimensional Physical Fiber

## Abstract

A finite-dimensional physical readout fiber is nonempty, compact, and convex.

**Theorem 1.1 (Finite-dimensional physical fibers are nonempty, compact, and convex).**

$$\operatorname{PhysFiber}_{O}(\rho) \neq \emptyset \land\\\operatorname{IsCompact}(\operatorname{PhysFiber}_{O}(\rho)) \land\\\operatorname{Convex}_{\mathbb{R}}(\operatorname{PhysFiber}_{O}(\rho)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/PhysicalFiber.finite_dimensional_physical_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite-dimensional complex matrix algebra, a positive trace-one state rho, and a finite family of accessible linear readouts. The physical fiber consists exactly of positive trace-one matrices whose accessible readout equals that of rho.

The fiber contains rho. It is closed because the readout equality, positive cone, and trace-one slice are closed, and it lies in the compact unit ball because a positive trace-one matrix has operator norm at most one.

Linearity preserves the fixed readout and trace under convex mixtures, while positive semidefiniteness is closed under nonnegative sums. Thus the same constructed fiber satisfies all three clauses.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/PhysicalFiber.finite_dimensional_physical_fiber`
