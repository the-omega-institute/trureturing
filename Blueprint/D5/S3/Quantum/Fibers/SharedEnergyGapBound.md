# Shared Energy Indecomposable Bound

## Abstract

Labelled indecomposable zero-weight exponents have degree at most twice m minus one.

**Theorem 1.1 (The bound includes zero units and repeated numerical gaps).**

$$\forall m\in\operatorname{Nat}(),2\leq m \implies \forall a\in\operatorname{Exponent}(),\operatorname{Indecomposable}(m,a) \implies \operatorname{degree}(a)\leq 2\cdot m-1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/SharedEnergyGapBound.indecomposable_degree_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain consists of actual labelled natural exponents on all nine ordered matrix coordinates for the fixed energy basis with energies zero, one and m. A nonzero zero-weight exponent is indecomposable when every zero-weight subexponent is zero or the whole exponent. If a diagonal coordinate occurs, its unit already forces degree one. If both directions of a coordinate occur, their pair forces degree two. Otherwise transpose if necessary to remove the positive m coordinate. The remaining sign patterns admit explicit zero-weight subexponents with degree at most twice m minus one. Minimality forces equality with one of those subexponents. Every step retains coordinate identity, so the coincident numerical gaps at m equal to two remain included. The degree bound combines with shared-moment extraction and support-wise phase reconstruction to give the all-state compact-orbit bound.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/SharedEnergyGapBound.indecomposable_degree_bound`
- Dependency: [D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold](SharedEnergyCopyThreshold.md)
