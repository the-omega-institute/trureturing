# Incomplete Observer Physical Counterexample

## Abstract

An incomplete finite observer has distinct symmetric states with equal readouts.

**Theorem 1.1 (An incomplete observer admits distinct indistinguishable physical states).**

$$\forall d\in \mathbb{N}, \operatorname{NeZero}\left(d\right), Index: \operatorname{Type},\\{}E: Index \to \operatorname{Herm}_{d}^{0},\\{}(\mathbb{R}I + \operatorname{span}\left(\mathbb{R}, \{E\left(i\right) \mid i: Index\}\right))^{\perp} \neq \{0\} \Rightarrow\\{}\exists D: \operatorname{Herm}_{d}, eps: \mathbb{R}, rhoPlus, rhoMinus: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\\{}D \neq 0 \land D \in (\mathbb{R}I + \operatorname{span}\left(\mathbb{R}, \{E\left(i\right) \mid i: Index\}\right))^{\perp} \land\\{}0 < eps \land\\{}\operatorname{matrix}\left(rhoPlus\right) = d^{{-1}}I + epsD \land\\{}\operatorname{matrix}\left(rhoMinus\right) = d^{{-1}}I - epsD \land\\{}rhoPlus \neq rhoMinus \land\\{}\forall i: Index, \Re \operatorname{Tr}\left(\operatorname{matrix}\left(rhoPlus\right) E\left(i\right)\right) = \Re \operatorname{Tr}\left(\operatorname{matrix}\left(rhoMinus\right) E\left(i\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/IncompleteObserverPhysicalCounterexample.incomplete_observer_physical_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The visible real Hermitian subspace is constructed from the scalar identity line and the embedded span of the centered effects. Incompleteness means that its orthogonal residual contains a nonzero direction.

A sufficiently small positive perturbation in both signs around the maximally mixed state remains positive and trace one. Orthogonality to every centered effect makes the two real trace signatures equal, while the nonzero direction makes the states distinct.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/IncompleteObserverPhysicalCounterexample.incomplete_observer_physical_counterexample`
- Dependency: [D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence](../Tomography/InformationalCompletenessEquivalence.md)
