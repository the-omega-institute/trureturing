# Low Cutoff Observation Fibres

## Abstract

Every instantaneous datum inside the unit frequency cutoff is a function of the pair alpha and alpha times beta.

**Definition 1.1 (lowCutoffDatum).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.lowCutoffDatum`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.lowCutoffDatum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete instantaneous datum visible inside the squared-frequency cutoff.

**Theorem 1.2 (lowCutoffDatum eq iff).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.lowCutoffDatum_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.lowCutoffDatum_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fibres of the low-cutoff datum are exactly the level sets of the pair alpha and alpha times beta.

**Definition 1.3 (cutoffGap).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoffGap`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoffGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A real-valued gap on the low-cutoff datum, built from the visible amplitude slot and the transverse acceleration slot.

**Theorem 1.4 (cutoffGap eq zero iff).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoffGap_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoffGap_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The gap vanishes exactly on the fibres.

**Definition 1.5 (UniformlyStableCutoffBetaRecovery).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.UniformlyStableCutoffBetaRecovery`

*Formalization.* `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.UniformlyStableCutoffBetaRecovery` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The claim that beta is recoverable from the low-cutoff datum with a modulus of continuity uniform over the whole family.

**Theorem 1.6 (not uniformlyStableCutoffBetaRecovery).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.not_uniformlyStableCutoffBetaRecovery`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.not_uniformlyStableCutoffBetaRecovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No uniform modulus exists: shrinking the visible amplitude makes the gap arbitrarily small while the hidden amplitudes stay a fixed distance apart.

**Theorem 1.7 (cutoff beta modulus on slab).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoff_beta_modulus_on_slab`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoff_beta_modulus_on_slab` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the slab where the visible amplitude is at least a, recovery of beta is Lipschitz with constant four over a.

**Theorem 1.8 (cutoff beta modulus on slab sharp).**

Lean statement: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoff_beta_modulus_on_slab_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoff_beta_modulus_on_slab_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The slab constant four over a is attained, so it cannot be improved.

## References

- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.UniformlyStableCutoffBetaRecovery`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoffGap`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoffGap_eq_zero_iff`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoff_beta_modulus_on_slab`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.cutoff_beta_modulus_on_slab_sharp`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.lowCutoffDatum`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.lowCutoffDatum_eq_iff`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/LowCutoffObservationFibres.not_uniformlyStableCutoffBetaRecovery`
- Dependency: [D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery](AugmentedReadoutRecovery.md)
