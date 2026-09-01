# Time-Shift Spectral Fiber Transport

## Abstract

Time translation becomes diagonal multiplication on spectral fibers and obeys an exact semigroup law.

**Theorem 1.1 (Transported readout equals translated time).**

$$\begin{gathered}\forall m, a, t, s:\\{}\operatorname{crystalTimeSample}(m, \operatorname{spectralFiberTransport}(m, s, a), t) = \operatorname{crystalTimeSample}(m, a, s + t).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/TimeShiftSpectralFiberTransport.crystal_time_sample_after_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Diagonal transport through a finite number of steps followed by a time readout equals reading the original amplitudes at the translated time.

The theorem is an exact semigroup identity for finite modal fibers. It supplies the typed bridge between time shifts and spectral multiplication.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/TimeShiftSpectralFiberTransport.crystal_time_sample_after_transport`
- Dependency: [D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge](FiniteCrystalTimeFrequencyBridge.md)
