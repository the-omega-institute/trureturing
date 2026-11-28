# Five-dimensional modular correction

## Abstract

The elementary five-dimensional null-diamond kernel and its weighted Hilbert–Schmidt factorization.

**Theorem 1.1 (Elementary boundary correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.correction5D_mixed_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.correction5D_mixed_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For positive radii and angular dot product below one, differentiate the scaled half-integer bulk difference in each radius. The two derivatives give the exponential times the linear factor in Appendix A.

**Theorem 1.2 (Real modular kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.kernelG5D_ofReal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.kernelG5D_ofReal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On the real axes the holomorphic kernel equals the boundary correction at the two logistic radii times both logistic Jacobians and the covariance factor four.

**Theorem 1.3 (Bounds on the modular roots).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.modularRoot_closedStrip_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.modularRoot_closedStrip_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On the closed strip of width 3/8, each root has modulus at most the reciprocal of the square root of cos(3π/8). The real part of their product is bounded below by the negative of that modulus bound squared.

**Theorem 1.4 (Exponential Fourier decay).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.fourierG5D_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.fourierG5D_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For each positive mass, the two-frequency kernel is bounded by a mass-dependent constant times the product of two exponentials of rate 3/8 and the inverse square root of one minus the angular dot product. The separate modular roots avoid the principal branch cut. Horizontal contour shifts give the two exponential factors.

**Definition 1.5 (Phase measure).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.phase5DMeasure`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.phase5DMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Use Lebesgue measure in frequency and round measure on the celestial three-sphere.

**Definition 1.6 (Normalized kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.tKernel5D`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.tKernel5D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Evaluate the two-frequency kernel at the angular dot product and divide by the product of the square roots of the radial normalization weights.

**Definition 1.7 (Inverse quarter weights).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.wKernel5D`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.wKernel5D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiply the normalized kernel by the inverse quarter power of the positive symbol in each frequency.

**Theorem 1.8 (Weighted square integrability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.wKernel5D_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.wKernel5D_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The inverse powers use at most 1/4 of the decay rate in each frequency, leaving rate 1/8. The angular square has finite integral on the product of round spheres.

**Definition 1.9 (Massless multiplier).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullA5D`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullA5D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The bounded operator A multiplies by 2/(1 + exp(ν)).

**Definition 1.10 (Centered multiplier).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullJ5D`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullJ5D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The bounded operator J equals A minus the identity.

**Definition 1.11 (Weighted integral operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullW5D`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullW5D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The operator W is realized by the inverse-quarter-weighted kernel.

**Definition 1.12 (Massive correction operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The operator T is realized by the normalized correction kernel.

**Theorem 1.13 (Hilbert–Schmidt weighted operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullW5D_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullW5D_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The operator W is Hilbert–Schmidt by the square-integrable kernel theorem.

**Theorem 1.14 (Hilbert–Schmidt massive correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The operator T is Hilbert–Schmidt by square integrability of the normalized kernel.

**Theorem 1.15 (Nonnegative massless operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullA5D_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullA5D_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The quadratic form of A integrates the positive frequency symbol against the squared modulus of the input.

**Theorem 1.16 (Trivial kernel of the centered multiplier).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullJ5D_ker`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullJ5D_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The symbol of J vanishes on the phase-space slice of frequency zero, which has measure zero. Thus J has trivial kernel.

**Theorem 1.17 (Self-adjoint massive correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D_selfAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Reality and exchange symmetry of the modular kernel give a Hermitian Fourier kernel by Fubini. The angular dot product and normalization are symmetric.

**Theorem 1.18 (Quarter-power factorization).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The positive fourth root of A is the pointwise quarter-power multiplier. Applying it on both sides of W cancels the two inverse weights and gives T.

**Definition 1.19 (Frequency conjugation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Reverse the frequency and conjugate pointwise to obtain an isometric, conjugate-linear involution.

**Theorem 1.20 (Almost-everywhere action).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A representative of the conjugated vector agrees almost everywhere with the complex conjugate evaluated at the negated frequency and original direction.

**Theorem 1.21 (Commutation with the massive correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D_comm_T`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D_comm_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Reflecting both frequencies conjugates the normalized Fourier kernel and preserves phase measure, so frequency conjugation commutes with T.

**Theorem 1.22 (Anticommutation with the centered multiplier).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D_anti_J`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D_anti_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The real symbol of J is odd, so frequency conjugation anticommutes with J.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.correction5D_mixed_deriv`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.fourierG5D_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.kernelG5D_ofReal`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.modularRoot_closedStrip_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullA5D`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullA5D_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D_ae`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D_anti_J`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullConj5D_comm_T`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullJ5D`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullJ5D_ker`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D_factor`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D_hs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullT5D_selfAdjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullW5D`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.nullW5D_hs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.phase5DMeasure`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.tKernel5D`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.wKernel5D`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.wKernel5D_memLp`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation](CCRConjugation.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D](NullDiamondContour4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS](NullDiamondKernelHS.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D](NullDiamondMultipliers4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D](NullDiamondSphere5D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt](QuarterPowerSqrtHilbertSchmidt.md)
