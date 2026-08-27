# Target Prediction Sufficiency

## Abstract

Visible targets are signature-determined; invisible targets separate physical states.

**Theorem 1.1 (The visible span is exactly sufficient for target prediction).**

$$\begin{gathered}\forall d\in \mathbb{N}, \operatorname{NeZero}(d), Index: \operatorname{Type},\\{}E: Index \to \{X: \operatorname{HermitianSpace}(d) \mid \operatorname{PosSemidef}(\operatorname{matrix}(X)) \land \operatorname{PosSemidef}(I - \operatorname{matrix}(X))\},\\{}T: \operatorname{Submodule}(\mathbb{R}, \operatorname{HermitianSpace}(d)),\\{}\operatorname{let} V: \operatorname{Submodule}(\mathbb{R}, \operatorname{HermitianSpace}(d)) = \operatorname{span}(\mathbb{R}, \operatorname{insert}(\operatorname{identityHermitian}(d), \operatorname{range}(E)))\;\\{}[T \subseteq V \Rightarrow \forall A: \operatorname{HermitianSpace}(d), A \in T, \rho, \sigma: \operatorname{DensityState}(\operatorname{Fin}(d)), (\forall i: Index, \operatorname{Tr}(\operatorname{matrix}(\rho) E\left(i\right)) = \operatorname{Tr}(\operatorname{matrix}(\sigma) E\left(i\right))) \Rightarrow \operatorname{Tr}(\operatorname{matrix}(\rho) A) = \operatorname{Tr}(\operatorname{matrix}(\sigma) A)] \land\\{}[\forall A: \operatorname{HermitianSpace}(d), \neg{A \in V} \Rightarrow\\{}\exists D: \operatorname{HermitianSpace}(d), eps: \mathbb{R}, rhoPlus, rhoMinus: \operatorname{DensityState}(\operatorname{Fin}(d)),\\{}\operatorname{Tr}(D) = 0 \land D \in V^{{\perp}} \land\\{}\operatorname{Tr}(D A) \neq 0 \land 0 < eps \land\\{}\operatorname{matrix}(rhoPlus) = d^{{-1}} I + eps D \land\\{}\operatorname{matrix}(rhoMinus) = d^{{-1}} I - eps D \land\\{}(\forall i: Index, \operatorname{Tr}(\operatorname{matrix}(rhoPlus) E\left(i\right)) = \operatorname{Tr}(\operatorname{matrix}(rhoMinus) E\left(i\right))) \land\\{}\operatorname{Tr}(\operatorname{matrix}(rhoPlus) A) \neq \operatorname{Tr}(\operatorname{matrix}(rhoMinus) A)].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PredictionDepth/TargetPredictionSufficiency.target_prediction_sufficiency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The visible real Hermitian subspace is constructed from the identity and the complete family of declared effects. If the target subspace lies inside it, equal physical-state signatures force equal expectations for every target observable.

For an observable outside the visible span, subtract its orthogonal projection. The resulting nonzero residual is trace zero and has a nonzero trace pairing with the observable.

Small symmetric perturbations of the maximally mixed state along that residual are density states. They agree on every current effect but have different expectation for the chosen observable.

## References

- Truth anchor: `D5/S3/Quantum/PredictionDepth/TargetPredictionSufficiency.target_prediction_sufficiency`
- Dependency: [D5/S3/Quantum/Measurement/IncompleteBudgetPhysicalCertificate](../Measurement/IncompleteBudgetPhysicalCertificate.md)
