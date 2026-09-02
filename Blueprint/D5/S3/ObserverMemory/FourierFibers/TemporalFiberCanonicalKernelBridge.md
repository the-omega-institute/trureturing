# Temporal Fiber Canonical-Kernel Bridge

## Abstract

Consecutive finite spectral time fibers are exactly the canonical future-readout kernels.

**Theorem 1.1 (Consecutive temporal fibers reuse the canonical observation kernel).**

$$\begin{gathered}\forall m, d:\\{}\operatorname{ker}(\operatorname{temporalWindowReadout}(m, \operatorname{range}(d + 1))) = \operatorname{observationSetoid}(\operatorname{oneStepSpectralUpdate}(m), \operatorname{modalSumReadout}(), d).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/TemporalFiberCanonicalKernelBridge.temporal_range_kernel_eq_observation_setoid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality kernel of the spectral readout on times zero through the selected depth is the repository's canonical observation setoid at that depth.

The proof identifies the finite spectral word with futureReadoutWord and introduces no parallel time-kernel hierarchy.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/TemporalFiberCanonicalKernelBridge.temporal_range_kernel_eq_observation_setoid`
- Dependency: [D5/S3/Observer/Separation/FiniteObservationRefinementBound](../../Observer/Separation/FiniteObservationRefinementBound.md)
- Dependency: [D5/S3/ObserverMemory/FourierFibers/SpectralFutureReadoutBridge](SpectralFutureReadoutBridge.md)
- Dependency: [D5/S3/ObserverMemory/FourierFibers/TemporalFiberObserverUpgrade](TemporalFiberObserverUpgrade.md)
