# Regulation on the null cone

## Abstract

Regulated shell squares and the smeared bulk correction.

**Definition 1.1 (Shell amplitude).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.shellAmplitude`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.shellAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Integrate the affine radius times the radial derivative against the momentum plane wave over the affine interval and round sphere.

**Definition 1.2 (Regulated shell square).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Integrate four times the shell density multiplied by the exponential energy damping and the squared modulus of the shell amplitude.

**Theorem 1.3 (Nonnegativity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The shell density, exponential damping, and square are nonnegative for every real mass and regulator.

**Theorem 1.4 (Regulated bulk pairing).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad_eq_bulk`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad_eq_bulk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At a positive regulator the shell square equals the real part of the double boundary pairing with the regulated bulk kernel. The damping and bounded affine derivative give the integrable majorant for Fubini.

**Theorem 1.5 (Limit of the shell difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad_difference_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad_difference_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The massive regulated shell square minus its massless counterpart converges to the real part of four times the smeared position-space correction.

**Theorem 1.6 (Massless angular denominator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.bulkU_zero_cap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.bulkU_zero_cap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiplying the zero-mass bulk kernel by four times the product of the two affine radii leaves the cap denominator with prefactor one divided by twice pi squared.

**Theorem 1.7 (Massless weak boundary).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.massless_boundary_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.massless_boundary_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

As the positive regulator tends to zero, the shell square converges to the real quadratic form of the massless multiplier on the weighted Fourier embedding. Subtracting the coincident angular value leaves a dominated integral that vanishes by radial cancellation. The cap primitive supplies the logarithmic form.

**Theorem 1.8 (Massive weak boundary).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.massive_boundary_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.massive_boundary_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For positive mass the limiting quadratic form includes the existing correction operator. The bulk difference has an integrable angular logarithm after smearing. Two radial integrations by parts and Fourier inversion identify it with the operator defined by the weighted correction kernel.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.bulkU_zero_cap`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.massive_boundary_limit`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.massless_boundary_limit`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad_difference_limit`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad_eq_bulk`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.regulatedShellQuad_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondWeakBoundary4D.shellAmplitude`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMassShell4D](NullDiamondMassShell4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D](NullDiamondMultipliers4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D](NullDiamondProfileFourier4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D](NullDiamondSphere4D.md)
