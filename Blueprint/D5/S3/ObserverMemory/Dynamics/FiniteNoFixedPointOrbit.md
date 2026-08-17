# Finite No-Fixed-Point Orbits

## Abstract

Every orbit of a finite fixed-point-free map enters a nontrivial cycle.

**Theorem 1.1 (Finite fixed-point-free orbits enter nontrivial cycles).**

$$\forall X,\ [\operatorname{Fintype} X],\ T: X \to X,\ (\forall x\in X, T(x) \neq x) \Rightarrow \forall x_{0}\in X,\ \exists mu, p\in \mathbb{N},\ mu+p \leq \operatorname{card}(X) \land 2 \leq p \land \forall t\in \mathbb{N},\ mu \leq t \Rightarrow T^{t+p}(x_{0}) = T^{t}(x_{0}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/FiniteNoFixedPointOrbit.finite_no_fixed_point_orbit_eventually_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a finite state carrier, T a self-map without fixed points, and x0 an initial state. There are a tail index mu and a period p whose sum is no larger than the number of states.

The period is at least two, and every time at or after mu returns to the same state after p further updates. This closes qdo-v1 theorem/38.8, atom qdo-residual-21a05dfa718331655905d64d470bc9e364bd37cfa07ff496de3eaa98fa613754.

Repository search supplied the quantitative finite-orbit theorem finite_orbit_and_readout_eventually_periodic, which is applied directly. Pinned Mathlib supplies its pigeonhole and iterate ingredients, but no declaration combining eventual periodicity with the fixed-point-free exclusion of period one.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/FiniteNoFixedPointOrbit.finite_no_fixed_point_orbit_eventually_periodic`
- Dependency: [D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound](../Prediction/FiniteOrbitPeriodBound.md)
