# Quasiperiodic Torus Flow

## Abstract

Finite-dimensional additive tori carry linear quasiperiodic flows and an integer combination-frequency module.

**Definition 1.1 (Finite phase torus).**

Lean statement: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.PhaseTorus`

*Formalization.* `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.PhaseTorus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A torus phase assigns one unit additive-circle coordinate to each finite frequency channel.

**Definition 1.2 (Linear quasiperiodic flow).**

Lean statement: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow`

*Formalization.* `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each phase coordinate is translated by time multiplied by its real frequency.

**Definition 1.3 (Integer combination frequency).**

Lean statement: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.combinationFrequency`

*Formalization.* `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.combinationFrequency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An integer mode vector pairs with the frequency vector by a finite dot product.

**Definition 1.4 (Exact resonant mode).**

Lean statement: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.IsResonantMode`

*Formalization.* `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.IsResonantMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A mode is resonant when its integer combination frequency vanishes.

**Theorem 1.5 (Zero time fixes the torus).**

Lean statement: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow_zero`

*Formalization.* `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The additive identity time contributes no circle translation.

**Theorem 1.6 (Flow times add).**

Lean statement: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow_add`

*Formalization.* `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Successive torus translations compose by addition of their real time parameters.

**Theorem 1.7 (Negative time reverses the flow).**

Lean statement: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow_neg_cancel`

*Formalization.* `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow_neg_cancel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation by a time followed by its negative returns every torus phase.

**Theorem 1.8 (Combination frequencies are additive).**

Lean statement: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.combinationFrequency_add`

*Formalization.* `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.combinationFrequency_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding two integer mode vectors adds their paired frequencies.

**Theorem 1.9 (Resonances form an additive family).**

Lean statement: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.isResonantMode_add`

*Formalization.* `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.isResonantMode_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum and negative of exact resonant modes remain resonant.

## References

- Truth anchor: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.PhaseTorus`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.combinationFrequency`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.IsResonantMode`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow_zero`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow_add`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.quasiperiodicFlow_neg_cancel`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.combinationFrequency_add`
- Truth anchor: `D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.isResonantMode_add`
- Dependency: [D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction](CommutingSpaceTimeAction.md)
