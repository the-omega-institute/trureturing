# Finite-Time Observer Monotonicity

## Abstract

Longer Heisenberg observation enlarges the visible span and shrinks its orthogonal residual.

**Theorem 1.1 (Visible spaces grow while orthogonal residuals shrink).**

$$\forall d\in Nat, r\in Nat, H: \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianSpace}(d), \operatorname{HermitianSpace}(d)), E: \operatorname{Fin}(r+1) \to \operatorname{HermitianSpace}(d)\Rightarrow\\{}\forall n\in Nat, \operatorname{span}(\mathbb{R}, \operatorname{insert}(\operatorname{identityHermitian}(d), \{E \mid \exists t\in \mathbb{N}, i\in \operatorname{Fin}(r+1), t < n \land E = H^{t}\left(E\left(i\right)\right)\})) \subseteq \operatorname{span}(\mathbb{R}, \operatorname{insert}(\operatorname{identityHermitian}(d), \{E \mid \exists t\in \mathbb{N}, i\in \operatorname{Fin}(r+1), t < n+1 \land E = H^{t}\left(E\left(i\right)\right)\})) \land \operatorname{orthogonal}(\operatorname{span}(\mathbb{R}, \operatorname{insert}(\operatorname{identityHermitian}(d), \{E \mid \exists t\in \mathbb{N}, i\in \operatorname{Fin}(r+1), t < n+1 \land E = H^{t}\left(E\left(i\right)\right)\}))) \subseteq \operatorname{orthogonal}(\operatorname{span}(\mathbb{R}, \operatorname{insert}(\operatorname{identityHermitian}(d), \{E \mid \exists t\in \mathbb{N}, i\in \operatorname{Fin}(r+1), t < n \land E = H^{t}\left(E\left(i\right)\right)\}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/FiniteTimeObserverMonotonicity.finite_time_observer_monotonicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the canonical real Hermitian matrix space. At horizon n, the visible space is constructed as the real span of the identity and every effect after a Heisenberg iterate t with t < n.

Each generator at horizon n is also a generator at horizon n+1, so the first public clause includes the smaller visible span in the larger one. Orthogonal complementation reverses that inclusion for the second public clause.

The theorem uses the source's finite-time test directly and introduces no parallel visible-space or residual definition.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/FiniteTimeObserverMonotonicity.finite_time_observer_monotonicity`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Measurement/BasisMeasurementProjection](../Measurement/BasisMeasurementProjection.md)
