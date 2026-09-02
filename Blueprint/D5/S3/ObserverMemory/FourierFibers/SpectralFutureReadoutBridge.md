# Spectral Future-Readout Bridge

## Abstract

The finite spectral time-delay word is exactly the repository's canonical future-readout word for diagonal modal transport.

**Theorem 1.1 (Spectral delays reuse the canonical future word).**

$$\begin{gathered}\forall m, d, a:\\{}\operatorname{futureReadoutWord}(\operatorname{oneStepSpectralUpdate}(m), \operatorname{modalSumReadout}(), d, a) = \operatorname{crystalTimeWord}(m, d, a).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/SpectralFutureReadoutBridge.future_readout_word_eq_crystal_time_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one-step diagonal spectral evolution and the modal-sum sensor, the repository's canonical finite future-readout word equals the finite crystal time word coordinatewise.

This bridge prevents a second delay-coordinate API and connects finite Koopman-style time-delay reasoning to the existing observer-completion machinery.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/SpectralFutureReadoutBridge.future_readout_word_eq_crystal_time_word`
- Dependency: [D5/S3/ObserverMemory/FourierFibers/TimeShiftSpectralFiberTransport](TimeShiftSpectralFiberTransport.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability](../Prediction/ConditionalEntropyStability.md)
