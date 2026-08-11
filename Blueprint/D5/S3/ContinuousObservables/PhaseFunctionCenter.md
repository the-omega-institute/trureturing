# The Phase-Function Center of Continuous Observables

## Abstract

The center of continuous cyclic-window matrix observables is the phase-function algebra.

**Theorem 1.1 (The continuous window center is the phase-function algebra).**

$$\forall M\in \mathbb{N}_{>0}, Z(C(\mathbb{T}, M_M(\mathbb{C}))) = \operatorname{range}(\operatorname{phaseScalarObservable}_M).$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/PhaseFunctionCenter.continuous_window_center_eq_phase_functions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty cyclic window, the center of the algebra of continuous matrix fields over the visible phase circle is exactly the range of scalar continuous fields. This identifies the center with the classical phase-function algebra C(T).

A central continuous matrix field commutes with every constant matrix field. Pointwise, Mathlib's matrix-center theorem forces it to be a scalar matrix. Reading one diagonal entry produces the continuous scalar function and proves surjectivity onto the center. Conversely, scalar matrices commute pointwise with every field.

## References

- Truth anchor: `D5/S3/ContinuousObservables/PhaseFunctionCenter.continuous_window_center_eq_phase_functions`
- Dependency: [D5/S3/Observer/CenterOperational](../Observer/CenterOperational.md)
