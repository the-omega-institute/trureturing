# Round measure on the celestial three-sphere

## Abstract

Round celestial measure and the inverse square-root angular singularity.

**Definition 1.1 (Round measure).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5DMeasure`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5DMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Equip the unit sphere in four-dimensional Euclidean space with the surface measure induced by Euclidean volume.

**Theorem 1.2 (Total mass).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_measure_univ`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_measure_univ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The round sphere has measure 2π², four times the volume of the four-dimensional unit ball.

**Theorem 1.3 (Distribution of the dot product).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_dot_pushforward`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_dot_pushforward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a fixed unit direction n, the dot product with n sends round measure to the density 4π√(1 − x²) on the interval from −1 to 1. Slice the solid cap of directions above a nonnegative threshold into three-dimensional balls. Integration of their volumes gives the upper tails, and reflection gives the lower half of the distribution.

**Theorem 1.4 (Orthogonal invariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_dot_rotation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_dot_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Every orthogonal transformation of the fixed direction yields the same dot-product distribution.

**Theorem 1.5 (Angular integration).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_dot_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_dot_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Integrating a measurable real function of the dot product against round measure gives its integral against the semicircle density on the interval from −1 to 1.

**Theorem 1.6 (Angular diagonal).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_diag_null`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_diag_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The pairs with dot product one form a null set for the product of round measures. Each angular section of this set has zero measure by the dot-product density.

**Theorem 1.7 (Integrable squared singularity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_inv_sqrt_sq_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_inv_sqrt_sq_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The reciprocal of one minus the dot product is integrable against product round measure. The substitution x = sin θ turns the normalized density divided by one minus x into 1 + sin θ on the interval from −π/2 to π/2.

**Theorem 1.8 (Exact singularity integral).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_inv_sqrt_sq_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_inv_sqrt_sq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The integral over the two spheres is 8π⁴. Each angular section contributes 4π² and the outer sphere contributes its total measure 2π².

**Theorem 1.9 (Square-integrable angular kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_inv_sqrt_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_inv_sqrt_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The inverse square root of one minus the dot product belongs to complex L² on the product sphere. This supplies angular control for the weighted Hilbert–Schmidt kernel in five dimensions.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5DMeasure`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_diag_null`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_dot_integral`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_dot_pushforward`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_dot_rotation`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_inv_sqrt_memLp`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_inv_sqrt_sq_integrable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_inv_sqrt_sq_integral`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D.sphere5D_measure_univ`
