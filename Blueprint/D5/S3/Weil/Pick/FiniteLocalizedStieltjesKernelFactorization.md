# Finite Localized Stieltjes Kernel Factorization

## Abstract

Finite atomic Stieltjes mass and support kernels factor through one Cauchy feature matrix and two diagonal weight matrices.

**Definition 1.1 (Finite atomic Stieltjes transform).**

Lean statement: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteAtomicStieltjesTransform`

*Formalization.* `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteAtomicStieltjesTransform` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The sum of the atomic Stieltjes transforms over a finite atom type.

**Definition 1.2 (Finite localized atomic Stieltjes transform).**

Lean statement: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteLocalizedAtomicStieltjesTransform`

*Formalization.* `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteLocalizedAtomicStieltjesTransform` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The finite sum after multiplication of every atomic transform by the spectral coordinate.

**Definition 1.3 (Finite mass kernel).**

Lean statement: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteMassKernel`

*Formalization.* `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteMassKernel` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The Hermitian sum of the atomic mass kernels.

**Definition 1.4 (Finite support kernel).**

Lean statement: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteSupportKernel`

*Formalization.* `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteSupportKernel` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The Hermitian sum of the mass-times-support atomic kernels.

**Definition 1.5 (Cauchy feature matrix).**

Lean statement: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.cauchyFeatureMatrix`

*Formalization.* `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.cauchyFeatureMatrix` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

Rows are sample points and columns are finite support atoms.

**Definition 1.6 (Mass weight matrix).**

Lean statement: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.massWeightMatrix`

*Formalization.* `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.massWeightMatrix` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The diagonal matrix of real atomic masses.

**Definition 1.7 (Support weight matrix).**

Lean statement: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.supportWeightMatrix`

*Formalization.* `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.supportWeightMatrix` (`✓ std3`).

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The diagonal matrix of mass-times-support localizing weights.

**Theorem 1.8 (Finite localization commutes with summation).**

$$\operatorname{Floc}\left(m, x, z\right) = z \cdot \operatorname{F}\left(m, x, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finite_localized_transform_eq_coordinate_mul` (`✓ std3`). ∎

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

A common spectral coordinate distributes across the finite atomic sum.

**Theorem 1.9 (The finite support kernel is the support-weighted atomic sum).**

$$\operatorname{Ksupport}\left(m, x, z, w\right) = \operatorname{supportWeightedMassKernelSum}\left(m, x, z, w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finite_support_kernel_eq_sum_support_mul_mass_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every atom keeps its own support coordinate, so no common scalar is extracted.

**Theorem 1.10 (The finite mass Gram matrix factors through Cauchy features).**

$$\operatorname{GramMass}\left(m, x, p\right) = \operatorname{C}\left(x, p\right) \cdot \operatorname{Dmass}\left(m\right) \cdot \operatorname{Cadjoint}\left(x, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finite_mass_gram_factorization` (`✓ std3`). ∎

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

The ordinary finite Gram matrix is C times the mass diagonal times C adjoint.

**Theorem 1.11 (The finite support Gram matrix factors through the localized diagonal).**

$$\operatorname{GramSupport}\left(m, x, p\right) = \operatorname{C}\left(x, p\right) \cdot \operatorname{DmassSupport}\left(m, x\right) \cdot \operatorname{Cadjoint}\left(x, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finite_support_gram_factorization` (`✓ std3`). ∎

*Citation.* Vladimir Derkach and Ivan Kovalyov (2017). *An operator approach to the indefinite Stieltjes moment problem*. DOI: [10.1007/s10958-017-3573-3](https://doi.org/10.1007/s10958-017-3573-3).

*Commentary.*

Coordinate localization changes only the diagonal from mass to mass times support.

## References

- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.cauchyFeatureMatrix`
- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteAtomicStieltjesTransform`
- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteLocalizedAtomicStieltjesTransform`
- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteMassKernel`
- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finiteSupportKernel`
- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finite_localized_transform_eq_coordinate_mul`
- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finite_mass_gram_factorization`
- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finite_support_gram_factorization`
- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.finite_support_kernel_eq_sum_support_mul_mass_kernel`
- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.massWeightMatrix`
- Truth anchor: `D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization.supportWeightMatrix`
- Dependency: [D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel](LocalizedStieltjesNevanlinnaKernel.md)
