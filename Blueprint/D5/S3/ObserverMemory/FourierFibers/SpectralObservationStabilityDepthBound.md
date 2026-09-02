# Spectral Observation Stability-Depth Bound

## Abstract

A separated finite diagonal spectrum stabilizes the canonical observer by the last required Vandermonde sample.

**Theorem 1.1 (Finite mode separation bounds canonical stability depth).**

$$\forall m, d, \operatorname{Injective}(m) \Rightarrow \operatorname{observationStabilityDepth}(\operatorname{oneStepSpectralUpdate}(m), \operatorname{modalSumReadout}()) \leq d.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/SpectralObservationStabilityDepthBound.spectral_observation_stability_depth_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For depth plus one pairwise distinct modes, the canonical future word through that depth is injective and its observation relation has already stabilized.

The theorem reuses observationStabilityDepth, futureReadoutWord, and finite Vandermonde tomography rather than defining a second temporal depth.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/SpectralObservationStabilityDepthBound.spectral_observation_stability_depth_le`
- Dependency: [D5/S3/Observer/Separation/FiniteObservationRefinementBound](../../Observer/Separation/FiniteObservationRefinementBound.md)
- Dependency: [D5/S3/ObserverMemory/FourierFibers/SpectralFutureReadoutBridge](SpectralFutureReadoutBridge.md)
