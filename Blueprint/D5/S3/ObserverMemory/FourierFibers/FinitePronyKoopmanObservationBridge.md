# Finite Prony to Koopman Observation Bridge

## Abstract

Finite Prony moments and shifted Hankel entries are exactly the existing diagonal spectral-fiber observations and delay coordinates.

**Theorem 1.1 (A Prony moment is a scalar spectral-fiber time sample).**

$$\operatorname{c}(t) = \operatorname{S}(x, w, t)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/FinitePronyKoopmanObservationBridge.finite_prony_moment_eq_crystal_time_sample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Prony moment and the repository's crystalTimeSample have the same weighted power-sum definition. The equality identifies the rational-transfer and observer-dynamics views without adding another time-sampling API.

**Theorem 1.2 (A shifted Hankel entry is a transported delay-coordinate sample).**

$$H_{s}(r, k) = \operatorname{S}(x, \operatorname{Phi}(x_{s})(w), r+k)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/FinitePronyKoopmanObservationBridge.finite_prony_shifted_hankel_entry_eq_transported_sample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Hankel entry at row and column delays is the scalar observation at their summed delay after the hidden amplitudes have undergone the requested diagonal spectral-fiber time shift.

Thus the shifted Hankel family is a finite Koopman-style delay table for the same hidden modal transport.

**Theorem 1.3 (Separated modes give a faithful first Prony delay window).**

$$\operatorname{Injective}(\operatorname{W}(x))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/FinitePronyKoopmanObservationBridge.finite_prony_first_window_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the modal nodes are distinct, the first matching number of Prony moments uniquely determines the hidden amplitude vector.

The proof reuses the frozen finite crystal-time observability theorem. It makes no infinite-delay, continuous-spectrum, or noisy embedding claim.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/FinitePronyKoopmanObservationBridge.finite_prony_first_window_injective`
- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/FinitePronyKoopmanObservationBridge.finite_prony_moment_eq_crystal_time_sample`
- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/FinitePronyKoopmanObservationBridge.finite_prony_shifted_hankel_entry_eq_transported_sample`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil](../../Analytic/GoldenTomography/FinitePronyMatrixPencil.md)
- Dependency: [D5/S3/ObserverMemory/FourierFibers/TimeShiftSpectralFiberTransport](TimeShiftSpectralFiberTransport.md)
