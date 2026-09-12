# Reversal Wave Synthesis

## Abstract

The reversal witness coefficients synthesize the stated smooth divergence-free real cosine fields.

**Definition 1.1 (character).**

Lean statement: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.character`

*Formalization.* `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.character` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The character exp(i*k.x), written in real sine/cosine coordinates.

**Definition 1.2 (synthesis).**

Lean statement: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.synthesis`

*Formalization.* `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.synthesis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal finite synthesis using the same four frequencies and coefficients.

**Definition 1.3 (realVelocity).**

Lean statement: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity`

*Formalization.* `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual smooth velocity field, independent of the third coordinate.

**Theorem 1.4 (synthesis eq realVelocity).**

Lean statement: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.synthesis_eq_realVelocity`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.synthesis_eq_realVelocity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Fourier data is exactly the advertised real cosine field.

**Theorem 1.5 (realVelocity contDiff).**

Lean statement: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity_contDiff`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both active spatial coordinates are jointly smooth to every finite order.

**Theorem 1.6 (realVelocity periodic).**

Lean statement: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity_periodic`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity_periodic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal field has the correct 2*pi period in each active coordinate.

**Theorem 1.7 (realVelocity divergence).**

Lean statement: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity_divergence`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity_divergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordinary coordinate derivatives give zero divergence; no symbolic 'divergence-free' label is used as a premise.

## References

- Truth anchor: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.character`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity_contDiff`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity_divergence`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.realVelocity_periodic`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.synthesis`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis.synthesis_eq_realVelocity`
- Dependency: [D5/S3/FluidDynamics/Fourier/LowModeReversalWitness](LowModeReversalWitness.md)
