# Dense-Orbit Invariant Rigidity

## Abstract

A continuous observable invariant under an update with a dense forward orbit is constant.

**Theorem 1.1 (A continuous dense-orbit invariant is constant).**

$$\forall X, Y,\ [\operatorname{TopologicalSpace}(X)] [\operatorname{TopologicalSpace}(Y)] [\operatorname{T2Space}(Y)],\ step: X \to X, observable: X \to Y, x_0: X,\ \operatorname{Continuous}(observable) \land \operatorname{DenseRange}((n\in \mathbb{N} \mapsto step^n(x_0))) \land\ (\forall x, observable(step(x)) = observable(x)) \Rightarrow\ \forall x, observable(x) = observable(x_0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/DenseOrbitInvariant.continuous_invariant_of_dense_orbit_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be an arbitrary topological space, Y a Hausdorff space, step an update on X, and observable a continuous map from X to Y. Assume the forward orbit of x0 is dense and observable is unchanged by every update. Then observable agrees everywhere with its value at x0.

Update invariance first propagates by induction along every finite iterate of the orbit. Mathlib's Continuous.ext_on then extends this equality from the dense orbit to all of X; Hausdorffness of Y is exactly the separation hypothesis used by that theorem.

Repository and pinned-Mathlib searches found no theorem combining forward iteration, invariance, and a dense orbit. Smart-search queries for continuous invariant functions on dense orbits and equality of continuous functions on dense sets identified Continuous.ext_on as the reusable extension theorem.

This result closes only the general dense-orbit mechanism in residual theorem 6.31. It does not formalize or claim the source theorem's full kernel-equals-center characterization.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/DenseOrbitInvariant.continuous_invariant_of_dense_orbit_constant`
