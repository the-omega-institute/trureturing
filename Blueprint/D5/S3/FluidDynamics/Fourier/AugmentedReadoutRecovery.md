# Augmented Readout Recovery

## Abstract

One instantaneous transverse acceleration reading recovers the hidden amplitude on the two-parameter Fourier witness family exactly when the visible amplitude is nonzero.

**Theorem 1.1 (low observation visible).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.low_observation_visible`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.low_observation_visible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The low observation at mode (1,0), component 1, is exactly alpha/2.

**Definition 1.2 (augmentedReadout).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmentedReadout`

*Formalization.* `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmentedReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete low observation paired with one instantaneous transverse acceleration component.

**Theorem 1.3 (alpha recovery).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.alpha_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.alpha_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice the real part of the visible observation recovers alpha.

**Theorem 1.4 (augmented readout im).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmented_readout_im`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmented_readout_im` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imaginary part of the additional reading is -alpha*beta/4.

**Theorem 1.5 (beta recovery).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.beta_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.beta_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero alpha, the additional reading recovers beta by explicit division.

**Theorem 1.6 (beta recovery from readout).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.beta_recovery_from_readout`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.beta_recovery_from_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonzero alpha, both readings alone explicitly reconstruct beta.

**Theorem 1.7 (augmented readout zero).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmented_readout_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmented_readout_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At alpha = 0, every beta gives the same low observation and zero additional reading.

**Theorem 1.8 (augmentedReadout eq iff).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmentedReadout_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmentedReadout_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two augmented readouts agree exactly when alpha agrees and either alpha is zero or beta agrees.

## References

- Truth anchor: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.alpha_recovery`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmentedReadout`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmentedReadout_eq_iff`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmented_readout_im`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.augmented_readout_zero`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.beta_recovery`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.beta_recovery_from_readout`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery.low_observation_visible`
- Dependency: [D5/S3/FluidDynamics/Fourier/LowModeReversalWitness](LowModeReversalWitness.md)
