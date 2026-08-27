# Finite Time Projection Kernel Antitonicity

## Abstract

Equality at a longer finite time projection implies equality at every shorter horizon.

**Theorem 1.1 (Longer-horizon equality restricts to every shorter horizon).**

$$\forall X, O: \operatorname{Type}, q: X \to O, tau: X \to X,\\{}N, M: \mathbb{N}, N \leq M, x, y: X,\\{}(\operatorname{futureReadoutWord}(tau, q, M, x) = \operatorname{futureReadoutWord}(tau, q, M, y)) \Rightarrow\\{}(\operatorname{futureReadoutWord}(tau, q, N, x) = \operatorname{futureReadoutWord}(tau, q, N, y)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionKernelAntitone.finite_time_projection_kernel_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any state space, readout, update, and horizons N less than or equal to M, equality of the complete readout words through M forces equality of the words through N.

The proof embeds each coordinate of Fin (N + 1) into Fin (M + 1) and restricts the assumed function equality along that embedding. Thus the equality kernel is antitone in the horizon.

## References

- Truth anchor: `D5/S3/ConceptDynamics/TimeProjection/FiniteTimeProjectionKernelAntitone.finite_time_projection_kernel_antitone`
- Dependency: [D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability](../../ObserverMemory/Prediction/ConditionalEntropyStability.md)
