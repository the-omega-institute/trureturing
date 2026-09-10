# Advection Closure Instance

## Abstract

The Fourier witness violates the mixed-term condition of the quadratic closure criterion in a five-mode Galerkin state space.

**Definition 1.1 (State).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.State`

*Formalization.* `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.State` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Five retained complex velocity amplitudes, regarded as a real vector space.

**Definition 1.2 (mode).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.mode`

*Formalization.* `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.mode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The generated transverse mode followed by the original four input modes.

**Definition 1.3 (embed).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.embed`

*Formalization.* `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.embed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Linear zero extension of the four input amplitudes to the five retained modes.

**Definition 1.4 (family).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.family`

*Formalization.* `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.family` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original two-amplitude family in the enlarged state space.

**Definition 1.5 (B).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.B`

*Formalization.* `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full retained convolution followed by Leray projection, bundled bilinearly over the reals.

**Definition 1.6 (L).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.L`

*Formalization.* `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The viscous Fourier multiplier on every retained mode.

**Definition 1.7 (P).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.P`

*Formalization.* `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The squared-frequency cutoff at one on the retained state.

**Theorem 1.8 (projection idempotent).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.projection_idempotent`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.projection_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The low-mode cutoff is an idempotent linear projection.

**Theorem 1.9 (family observation).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.family_observation`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.family_observation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The projected family is exactly the original complete low observation sampled at retained modes.

**Theorem 1.10 (family acceleration).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.family_acceleration`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.family_acceleration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Galerkin vector field agrees with the fluid acceleration at every retained output on the family.

**Theorem 1.11 (mixed witness).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.mixed_witness`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.mixed_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A visible wave and a hidden wave have a nonzero observed mixed interaction.

**Theorem 1.12 (hidden linear).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.hidden_linear`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.hidden_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Viscosity preserves the kernel of the low-mode projection.

**Theorem 1.13 (mixed condition fails).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.mixed_condition_fails`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.mixed_condition_fails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The third condition of the general quadratic closure criterion fails.

**Theorem 1.14 (no exact closure).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.no_exact_closure`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.no_exact_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This concrete Galerkin instance has no exact closure, by the general quadratic criterion.

**Theorem 1.15 (exact closure implies fluid predictor).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.exact_closure_implies_fluid_predictor`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.exact_closure_implies_fluid_predictor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any global exact vector closure would predict the original transverse fluid coefficient on the family.

**Theorem 1.16 (fluid gap from mixed).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.fluid_gap_from_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.fluid_gap_from_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same mixed obstruction gives a fluid acceleration gap through the general observed-increment identity.

**Theorem 1.17 (no fluid predictor from mixed).**

Lean statement: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.no_fluid_predictor_from_mixed`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.no_fluid_predictor_from_mixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mixed obstruction re-derives exactly the original scalar predictor impossibility on the whole family.

## References

- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.B`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.L`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.P`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.State`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.embed`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.exact_closure_implies_fluid_predictor`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.family`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.family_acceleration`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.family_observation`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.fluid_gap_from_mixed`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.hidden_linear`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.mixed_condition_fails`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.mixed_witness`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.mode`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.no_exact_closure`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.no_fluid_predictor_from_mixed`
- Truth anchor: `D5/S3/FluidDynamics/Fourier/AdvectionClosureInstance.projection_idempotent`
- Dependency: [D5/S3/FluidDynamics/Fourier/LowModeReversalWitness](LowModeReversalWitness.md)
- Dependency: [D5/S3/Observer/Reversal/QuadraticObservationClosure](../../Observer/Reversal/QuadraticObservationClosure.md)
