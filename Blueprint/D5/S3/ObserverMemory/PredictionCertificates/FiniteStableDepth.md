# Finite Stable Depth

## Abstract

A finite state space reaches its complete prediction relation at a finite depth.

**Theorem 1.1 (Finite states have a stable prediction depth).**

$$\forall X: Type, I: Type, J: \operatorname{Finset}\left(I\right), O: (i: I) \to Type,\\{}[\operatorname{Finite}(X)], F: X \to X, q: (i: I) \to X \to O_i,\\{}\exists m \in \mathbb{N},\\{}\operatorname{finiteHorizonKernel}\left(F, \operatorname{jointObservation}\left(q_{J}\right), m\right) = \operatorname{ker}\left(\operatorname{completeItinerary}\left(F, \operatorname{jointObservation}\left(q_{J}\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionCertificates/FiniteStableDepth.finite_state_has_stable_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a finite state type, I the ambient interface type, J a finite subset of I, F a deterministic self-map, and q_i the readout at interface i. Applying jointObservation to q restricted to J gives the source's joint readout q_J.

At depth m, finiteHorizonKernel is the equality relation induced by the indexed readout word through times zero to m. The relation on the right is the equality kernel of completeItinerary, which records the same indexed readouts at every natural time.

The theorem asserts exactly one conclusion: some natural depth makes these two relations equal. Repository declaration finite_horizon_stabilizes_at_completionDepth supplies that equality after the finite state instance is made available; no second readout, relation, or stabilization proof is introduced.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionCertificates/FiniteStableDepth.finite_state_has_stable_depth`
- Dependency: [D5/S3/ObserverMemory/Prediction/JointPredictionRelation](../Prediction/JointPredictionRelation.md)
- Dependency: [D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence](../RefinementClosure/FiniteHorizonKernelRecurrence.md)
