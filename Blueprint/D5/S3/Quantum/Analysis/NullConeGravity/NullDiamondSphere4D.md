# Round measure on the celestial two-sphere

## Abstract

Round celestial measure and square integrability of the angular logarithm.

**Definition 1.1 (Round measure).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphereMeasure`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphereMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Equip the unit sphere in three-dimensional Euclidean space with the sphere measure induced by Euclidean volume.

**Theorem 1.2 (Distribution of the dot product).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_dot_pushforward`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_dot_pushforward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every fixed unit vector n, the dot product with n sends round measure to 2π times Lebesgue measure on the closed interval from −1 to 1. Slice the solid cone of directions above a nonnegative threshold into planar disks. Their areas give the upper-tail measure, and reflection handles negative thresholds.

**Theorem 1.3 (Total mass).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_measure_univ`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_measure_univ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The round sphere has measure 4π.

**Theorem 1.4 (Angular diagonal).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_diag_null`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_diag_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The pairs with dot product one form a null set for the product of round measures. For each fixed first coordinate the dot-product distribution assigns zero mass to one.

**Theorem 1.5 (Logarithm squared near zero).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.intervalIntegrable_log_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.intervalIntegrable_log_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The square of the real logarithm is interval integrable from zero to two.

**Theorem 1.6 (Square-integrable angular logarithm).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_log_sq_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_log_sq_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Apply the dot-product distribution and the substitution t = 1 − x in each angular section. The squared logarithm of one minus the dot product is integrable on the product sphere. This supplies the angular integrability used in the square-root trace criterion of Satishchandran and Sorce.

**Theorem 1.7 (Angular integral).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_log_sq_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_log_sq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The integral of the squared angular logarithm over the product sphere equals 8π² times the integral of the squared logarithm from zero to two.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.intervalIntegrable_log_sq`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphereMeasure`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_diag_null`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_dot_pushforward`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_log_sq_integrable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_log_sq_integral`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D.sphere_measure_univ`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy](../../../Arith/Robin/ForwardKernel/ClippedLogEnergy.md)
