# Localized Stieltjes and Nevanlinna Kernels

## Abstract

An atomic Stieltjes transform and its coordinate-localized transform have exact Nevanlinna kernels whose scalar weights are mass and mass times support.

**Definition 1.1 (Real-support Cauchy feature).**

Lean statement: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.stieltjesFeature`

*Formalization.* `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.stieltjesFeature` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The inverse affine distance from a complex sample to a real support coordinate.

**Definition 1.2 (Atomic Stieltjes transform).**

Lean statement: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomicStieltjesTransform`

*Formalization.* `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomicStieltjesTransform` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

A real atomic mass divided by support minus the complex sample.

**Definition 1.3 (Coordinate-localized atomic Stieltjes transform).**

Lean statement: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.localizedAtomicStieltjesTransform`

*Formalization.* `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.localizedAtomicStieltjesTransform` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

Multiplication by the spectral coordinate is the first Stieltjes support localizer.

**Definition 1.4 (Regular Stieltjes sample pair).**

Lean statement: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.regularStieltjesPair`

*Formalization.* `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.regularStieltjesPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support denominators and the Nevanlinna cross denominator are all nonzero.

**Definition 1.5 (Raw Nevanlinna difference quotient).**

Lean statement: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.rawNevanlinnaDifferenceQuotient`

*Formalization.* `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.rawNevanlinnaDifferenceQuotient` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The divided conjugate difference of the atomic Stieltjes transform.

**Definition 1.6 (Localized Nevanlinna difference quotient).**

Lean statement: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.localizedNevanlinnaDifferenceQuotient`

*Formalization.* `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.localizedNevanlinnaDifferenceQuotient` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The divided conjugate difference after multiplying the transform by the spectral coordinate.

**Definition 1.7 (Atomic mass kernel).**

Lean statement: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomicMassKernel`

*Formalization.* `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomicMassKernel` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The rank-one Hermitian Cauchy kernel whose scalar weight is the atomic mass.

**Definition 1.8 (Atomic support kernel).**

Lean statement: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomicSupportKernel`

*Formalization.* `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomicSupportKernel` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The rank-one Hermitian Cauchy kernel whose scalar weight is mass times support.

**Definition 1.9 (Normalized upper-half-plane sample).**

Lean statement: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.normalizedUpperSample`

*Formalization.* `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.normalizedUpperSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sample one imaginary unit above the real support atom.

**Theorem 1.10 (Support localization multiplies the mass kernel by support).**

$$\operatorname{supportKernel}\left(m, x, z, w\right) = x \cdot \operatorname{massKernel}\left(m, x, z, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomic_support_kernel_eq_support_mul_mass_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two kernels use the same Cauchy feature. Their only difference is the support coordinate in the scalar weight, so localization is exact and does not require a limiting argument.

**Theorem 1.11 (The raw difference quotient is the mass kernel).**

$$\operatorname{regularStieltjesPair}\left(x, z, w\right) \Rightarrow \operatorname{rawNevanlinnaDifferenceQuotient}\left(m, x, z, w\right) = \operatorname{massKernel}\left(m, x, z, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.raw_nevanlinna_difference_quotient_eq_mass_kernel` (`✓ std3`). ∎

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

For a regular sample pair, the conjugate divided difference of the atomic Stieltjes transform factors as the rank-one Cauchy kernel with mass weight.

**Theorem 1.12 (The localized difference quotient is the support kernel).**

$$\operatorname{regularStieltjesPair}\left(x, z, w\right) \Rightarrow \operatorname{localizedNevanlinnaDifferenceQuotient}\left(m, x, z, w\right) = \operatorname{supportKernel}\left(m, x, z, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.localized_nevanlinna_difference_quotient_eq_support_kernel` (`✓ std3`). ∎

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

Multiplication of the transform by z inserts the real support coordinate into the same rank-one Cauchy factor. This is the finite atomic form of the generalized Stieltjes distinction between f and z f.

**Theorem 1.13 (The normalized diagonal separates mass from support).**

$$m > 0 \Rightarrow (\operatorname{massKernelDiagonal}\left(m, x\right) = m \land \operatorname{supportKernelDiagonal}\left(m, x\right) = m \cdot x \land (\Re{\operatorname{supportKernelDiagonal}\left(m, x\right)} < 0 \iff x < 0)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.normalized_diagonal_reads_mass_and_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the sample support plus i, the Cauchy feature has unit modulus. The raw kernel therefore reads mass exactly, while the localized kernel reads mass times support exactly.

For strictly positive mass, the localized diagonal is negative exactly when the support coordinate is negative. The raw diagonal contains no such support-sign information.

## References

- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomicMassKernel`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomicStieltjesTransform`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomicSupportKernel`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.atomic_support_kernel_eq_support_mul_mass_kernel`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.localizedAtomicStieltjesTransform`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.localizedNevanlinnaDifferenceQuotient`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.localized_nevanlinna_difference_quotient_eq_support_kernel`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.normalizedUpperSample`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.normalized_diagonal_reads_mass_and_support`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.rawNevanlinnaDifferenceQuotient`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.raw_nevanlinna_difference_quotient_eq_mass_kernel`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.regularStieltjesPair`
- Truth anchor: `D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel.stieltjesFeature`
- Dependency: [D5/S3/Weil/Pick/HermitianKernelNegativeSquares](HermitianKernelNegativeSquares.md)
