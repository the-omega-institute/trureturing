# Low Mode Reversal Witness

## Abstract

An explicit two-amplitude incompressible Fourier family has identical low-mode reversals and distinct Leray-projected accelerations.

**Definition 1.1 (Mode).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.Mode`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.Mode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Integer planar frequencies, embedded in three-space with zero third entry.

**Definition 1.2 (Amplitude).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.Amplitude`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.Amplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three velocity components.

**Definition 1.3 (frequencySquared).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.frequencySquared`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.frequencySquared` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact integer squared frequency, with no floating comparison.

**Definition 1.4 (frequency).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.frequency`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.frequency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four modes of the two real cosine waves.

**Definition 1.5 (inputAmplitude).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.inputAmplitude`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.inputAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Real cosine amplitudes split equally across each conjugate frequency pair.

**Definition 1.6 (coefficient).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.coefficient`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual coefficient, summing every occurrence of an input frequency.

**Definition 1.7 (lowObservation).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.lowObservation`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.lowObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full low-frequency coefficient function.

**Definition 1.8 (advection).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.advection`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.advection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fourier coefficient of (u dot grad)u, computed by the full input convolution.

**Definition 1.9 (leray).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.leray`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.leray` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Leray's multiplier I-kk^T/|k|^2, including the identity at k=0. The zero-frequency formula is meaningful because both wave coordinates vanish.

**Definition 1.10 (acceleration).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.acceleration`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.acceleration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual viscous Fourier multiplier minus the Leray-projected nonlinearity.

**Theorem 1.11 (input divergence free).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.input_divergence_free`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.input_divergence_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every input coefficient is perpendicular to its actual frequency.

**Theorem 1.12 (conjugate pair data).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.conjugate_pair_data`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.conjugate_pair_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal real amplitudes at each opposite-frequency pair.

**Theorem 1.13 (lowObservation independent).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.lowObservation_independent`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.lowObservation_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The low observation forgets beta at every output frequency and component.

**Theorem 1.14 (transverse acceleration).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.transverse_acceleration`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.transverse_acceleration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The output coefficient is derived symbolically for every viscosity and both continuous amplitudes. It is not an assumed finite table entry.

**Theorem 1.15 (full partial reversal separation).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.full_partial_reversal_separation`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.full_partial_reversal_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full reversal (-1,-1) and visible-only reversal (-1,1) have the same entire low-frequency state and a nonzero low-frequency acceleration gap.

**Theorem 1.16 (low mode prediction error floor).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.low_mode_prediction_error_floor`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.low_mode_prediction_error_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every deterministic predictor from the same complete low-mode state has error at least 1/4 on one of the two actual complex acceleration coefficients.

**Theorem 1.17 (no low mode acceleration closure).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.no_low_mode_acceleration_closure`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.no_low_mode_acceleration_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No state-only predictor can recover this actual low acceleration on the whole two-amplitude family, including for every fixed positive viscosity.

## References

- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.Amplitude`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.Mode`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.acceleration`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.advection`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.coefficient`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.conjugate_pair_data`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.frequency`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.frequencySquared`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.full_partial_reversal_separation`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.inputAmplitude`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.input_divergence_free`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.leray`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.lowObservation`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.lowObservation_independent`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.low_mode_prediction_error_floor`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.no_low_mode_acceleration_closure`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowModeReversalWitness.transverse_acceleration`
