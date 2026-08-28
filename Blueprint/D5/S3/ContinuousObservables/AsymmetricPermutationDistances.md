# Asymmetric Permutation Observer Distances

## Abstract

Invariant-label separation for one update and orbit reachability for another produce asymmetric observer distances.

**Theorem 1.1 (Two permutation observers can assign infinite and finite distance).**

$$\forall I, Leaf, tau, tauPrime \in \operatorname{EquivPerm}(I), leaf \in \operatorname{Map}(I, Leaf), x, y \in I, n \in \mathbb{Z},\ \operatorname{InvariantLabel}(tau, leaf) \land leaf(x) \neq leaf(y) \land x = \operatorname{act}(tauPrime^{n}, y) \Rightarrow \operatorname{observerDistance}(tau, x, y) = \infty \land \operatorname{observerDistance}(tauPrime, x, y) \leq \left|n\right| \land \operatorname{observerDistance}(tauPrime, x, y) < \infty.$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/AsymmetricPermutationDistances.asymmetric_permutation_observer_distances` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bounded indicator of the first update's invariant label separates the endpoints, so its scalable zero-defect readout forces infinite distance.

For the second update, the signed orbit witness gives a telescoping unit-edge bound. The natural absolute displacement is explicitly finite in the extended nonnegative reals.

## References

- Truth anchor: `D5/S3/ContinuousObservables/AsymmetricPermutationDistances.asymmetric_permutation_observer_distances`
- Dependency: [D5/S3/ContinuousObservables/PermutationOrbitHorizon](PermutationOrbitHorizon.md)
