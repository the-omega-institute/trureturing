# Temporal Reflection-Break Visibility

## Abstract

A static scalar readout identifies reflected modal branches, while one nondegenerate time step separates them.

**Theorem 1.1 (Time reveals a nondegenerate reflected split).**

$$\forall z: \mathbb{C}, z \neq z^{-1} \Rightarrow \operatorname{crystalTimeSample}(\operatorname{reflectedModes}(z), \operatorname{firstBranch}(), 1) \neq \operatorname{crystalTimeSample}(\operatorname{reflectedModes}(z), \operatorname{secondBranch}(), 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/TemporalReflectionBreakVisibility.reflected_branches_time_one_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two reflected branch states collide at time zero. If their modal multipliers differ, the first time step produces different scalar readings.

The result formalizes temporal revelation of a pre-existing hidden distinction. It does not claim that the underlying difference is created by observation.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/TemporalReflectionBreakVisibility.reflected_branches_time_one_separation`
- Dependency: [D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge](FiniteCrystalTimeFrequencyBridge.md)
