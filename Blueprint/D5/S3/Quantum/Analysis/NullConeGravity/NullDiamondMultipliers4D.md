# Weighted kernel factorization and conjugation

## Abstract

Square-integrable weighted kernels and frequency conjugation on the four-dimensional null diamond.

The phase space carries Lebesgue frequency measure and round angular measure. The massive correction acts by an integral kernel on complex square-integrable functions. The massless part acts by a bounded real frequency multiplier.

**Definition 1.1 (Radial normalization).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wgt`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wgt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At real frequency ν the weight is ν cosh(ν/2) divided by sinh(ν/2), with value 2 at zero.

**Definition 1.2 (Positive symbol).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.a`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The real multiplier at frequency ν is 2/(1 + exp(ν)).

**Definition 1.3 (Centered symbol).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.freqJ`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.freqJ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The centered symbol is the positive symbol minus one.

**Theorem 1.4 (Bounds on the radial normalization).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wgt_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wgt_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every real ν the weight is at least 2 and at least |ν|, and at most 2 + |ν|.

**Definition 1.5 (Normalized massive correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.tKernel`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.tKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Evaluate the two-frequency Fourier kernel at the angular dot product and divide by the product of the square roots of the two radial weights.

**Definition 1.6 (Inverse quarter weights).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wKernel`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wKernel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiply the normalized kernel by the inverse quarter powers of the positive symbol in the two frequency variables.

**Theorem 1.7 (Weighted square integrability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wKernel_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wKernel_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every positive mass the weighted kernel is in L² of the product phase measure. The strip decay of rate 3/8 absorbs growth of rate 1/4 in each variable. The squared majorant separates into two integrable radial exponentials of rate 1/4 and an integrable squared angular logarithm.

**Definition 1.8 (Massless multiplier operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullA`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The bounded operator A multiplies by the positive symbol.

**Definition 1.9 (Centered multiplier operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullJ`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullJ` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The bounded operator J equals A minus the identity.

**Definition 1.10 (Weighted integral operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullW`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullW` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For each positive mass W is the integral operator with the inverse-quarter-weighted kernel.

**Definition 1.11 (Massive integral operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For each positive mass T is the integral operator with the normalized correction kernel.

**Theorem 1.12 (Hilbert–Schmidt weighted operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullW_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullW_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every positive mass W is Hilbert–Schmidt by the square-integrable kernel realization.

**Theorem 1.13 (Hilbert–Schmidt massive correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every positive mass T is Hilbert–Schmidt. Its kernel has the full contour decay rate.

**Theorem 1.14 (Massless positivity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullA_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullA_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The operator A is nonnegative because its quadratic form integrates the positive symbol against the squared modulus of the input.

**Theorem 1.15 (Quarter-power factorization).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every positive mass T equals A to the quarter power times W times A to the quarter power. Two applications of uniqueness of the positive square root identify the fourth root with the pointwise quarter-power multiplier. Its two symbol factors cancel the inverse weights.

**Theorem 1.16 (Self-adjoint massive correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT_selfAdjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT_selfAdjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every positive mass T is self-adjoint. Reality and exchange symmetry of the position kernel give a Hermitian Fourier kernel by Fubini.

**Theorem 1.17 (Trivial kernel of the centered multiplier).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullJ_ker`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullJ_ker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The kernel of J is the zero submodule. Its symbol can vanish only on the phase-space slice with frequency zero, which has measure zero.

**Definition 1.18 (Frequency conjugation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Conjugation after reversal of the frequency defines a real-linear isometric equivalence of the phase Hilbert space.

**Theorem 1.19 (Almost-everywhere action).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every input the output agrees almost everywhere with the complex conjugate of the input evaluated at the negated frequency and the original angular direction.

**Theorem 1.20 (Conjugate linearity).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every input and complex scalar, conjugating the scalar multiple multiplies the conjugated input by the conjugate of the scalar.

**Theorem 1.21 (Involution).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Applying frequency conjugation twice gives the original input.

**Theorem 1.22 (Commutation with the massive correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_comm_T`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_comm_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every positive mass and input, frequency conjugation commutes with T. Reflection of both frequencies conjugates the Fourier kernel and preserves the frequency measure.

**Theorem 1.23 (Anticommutation with the centered multiplier).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_anti_J`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_anti_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every input frequency conjugation sends J applied to the input to minus J applied to the conjugated input, because the centered frequency symbol is odd.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.a`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.freqJ`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullA`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullA_nonneg`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_ae`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_anti_J`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_comm_T`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_involutive`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullConj_smul`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullJ`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullJ_ker`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT_factor`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT_hs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullT_selfAdjoint`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullW`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.nullW_hs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.tKernel`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wKernel`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wKernel_memLp`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wgt`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.wgt_bounds`
- Dependency: [D5/S3/Analytic/Asymptotics/ExponentialAbsIntegrability](../../../Analytic/Asymptotics/ExponentialAbsIntegrability.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D](NullDiamondContour4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS](NullDiamondKernelHS.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D](NullDiamondSphere4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt](QuarterPowerSqrtHilbertSchmidt.md)
