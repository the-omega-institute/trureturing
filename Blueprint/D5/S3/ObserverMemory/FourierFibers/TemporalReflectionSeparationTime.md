# Temporal Reflection Separation Time

## Abstract

A nondegenerate reflected spectral pair has canonical first-separation time one.

**Theorem 1.1 (Reflected branches first separate at time one).**

$$\begin{gathered}\forall z: \mathbb{C}, z \neq z^{-1} \Rightarrow\\{}\operatorname{separationTime}(\operatorname{oneStepSpectralUpdate}(\operatorname{reflectedModes}(z)), \operatorname{modalSumReadout}(), (\operatorname{firstBranch}(), \operatorname{secondBranch}())) = 1.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/TemporalReflectionSeparationTime.reflected_branch_separation_time_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reflected branch states collide at time zero and, when their reciprocal multipliers differ, separate at the first subsequent observation.

The proof instantiates the repository's canonical separationTime and observedAt APIs; it does not introduce another break-depth definition.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/TemporalReflectionSeparationTime.reflected_branch_separation_time_eq_one`
- Dependency: [D5/S3/Observer/Separation/FiniteFutureCongruence](../../Observer/Separation/FiniteFutureCongruence.md)
- Dependency: [D5/S3/ObserverMemory/FourierFibers/SpectralFutureReadoutBridge](SpectralFutureReadoutBridge.md)
- Dependency: [D5/S3/ObserverMemory/FourierFibers/TemporalReflectionBreakVisibility](TemporalReflectionBreakVisibility.md)
