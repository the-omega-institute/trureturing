# Finite Crystal Time-Frequency Bridge

## Abstract

Distinct finite crystal modes are exactly reconstructible from an equally long scalar time window.

**Theorem 1.1 (Separated modes are recovered from time samples).**

$$\forall omega, \operatorname{Injective}(omega) \Rightarrow \operatorname{Injective}(\operatorname{firstCrystalTimeWindow}(omega)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge.first_crystal_time_window_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finitely many distinct modal multipliers, the first matching number of scalar time samples uniquely recovers all modal amplitudes.

This is a finite diagonal spectral realization of Vandermonde tomography. It does not construct an infinite Bloch bundle or identify the sampling index with physical time.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge.first_crystal_time_window_injective`
- Dependency: [D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography](../../Analytic/GoldenTomography/FiniteVandermondeTomography.md)
