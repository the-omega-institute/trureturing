# No Uniform Infinite-Future Stability Radius

## Abstract

Golden mechanical readouts have finite local stability but no uniform infinite-future radius.

**Theorem 1.1 (Boundary-driven prediction escape under an isometric circle update).**

$$(\forall \theta, \varepsilon>0, \exists \theta', n, \operatorname{d}(\theta', \theta) < \varepsilon \land w_{n}(\theta') \neq w_{n}(\theta)) \land\\(\forall N, \theta, \neg \operatorname{goldenObserverPrefixBoundary}(N, \theta) \Rightarrow \exists \varepsilon>0, \forall \theta', \operatorname{d}(\theta', \theta) < \varepsilon \Rightarrow \forall n<N, w_{n}(\theta') = w_{n}(\theta)) \land\\(\forall \theta, \neg \exists \varepsilon>0, \forall \theta', \operatorname{d}(\theta', \theta) < \varepsilon \Rightarrow \forall n, w_{n}(\theta') = w_{n}(\theta)) \land\\(\forall n, \theta, \theta', \operatorname{d}(R^{n}(\theta'), R^{n}(\theta)) = \operatorname{d}(\theta', \theta)) \land\\(\forall \theta, \varepsilon>0, \exists \theta', n, \operatorname{d}(\theta', \theta) < \varepsilon \land w_{n}(\theta') \neq w_{n}(\theta) \land \operatorname{d}(R^{n}(\theta'), R^{n}(\theta)) = \operatorname{d}(\theta', \theta)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/SymbolicStability/NoUniformInfiniteFutureRadius.no_uniform_infinite_future_stability_radius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem uses the literal golden slope phi^-2 and the integer floor-difference readout from the source construction. Its boundary set is the integer-lifted union of the first N + 1 cuts, and its update is addition by the same slope on the unit circle.

Every real phase has arbitrarily close phases whose integer readouts separate at some future coordinate. Consequently no positive radius stabilizes the entire future, while every finite prefix has a positive common radius away from its lifted boundary set.

The off-boundary condition is essential: finite-prefix stability is not asserted at a cut. Every iterate of the circle update preserves the initial distance exactly, and the final witnesses combine readout escape with that distance invariance.

## References

- Truth anchor: `D5/S3/Observer/SymbolicStability/NoUniformInfiniteFutureRadius.no_uniform_infinite_future_stability_radius`
- Dependency: [D5/S1/Words/Complexity/MechanicalSubshiftIntercept](../../../S1/Words/Complexity/MechanicalSubshiftIntercept.md)
- Dependency: [D5/S3/Observer/SymbolicStability/FinitePrefixLocalConstancy](FinitePrefixLocalConstancy.md)
