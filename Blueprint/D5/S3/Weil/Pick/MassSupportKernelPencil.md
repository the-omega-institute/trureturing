# Mass-Support Kernel Pencil

## Abstract

Dual Cauchy features recover finite support coordinates as genuine generalized eigenvalues of the localized mass-support Gram pencil.

**Definition 1.1 (Mass Gram matrix).**

Lean statement: `D5/S3/Weil/Pick/MassSupportKernelPencil.massGramMatrix`

*Formalization.* `D5/S3/Weil/Pick/MassSupportKernelPencil.massGramMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite ordinary Stieltjes Gram matrix.

**Definition 1.2 (Support Gram matrix).**

Lean statement: `D5/S3/Weil/Pick/MassSupportKernelPencil.supportGramMatrix`

*Formalization.* `D5/S3/Weil/Pick/MassSupportKernelPencil.supportGramMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite coordinate-localized Stieltjes Gram matrix.

**Definition 1.3 (Mass-support kernel pencil).**

Lean statement: `D5/S3/Weil/Pick/MassSupportKernelPencil.massSupportKernelPencil`

*Formalization.* `D5/S3/Weil/Pick/MassSupportKernelPencil.massSupportKernelPencil` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support Gram matrix minus a real parameter times the mass Gram matrix.

**Definition 1.4 (Shifted support weight matrix).**

Lean statement: `D5/S3/Weil/Pick/MassSupportKernelPencil.shiftedSupportWeightMatrix`

*Formalization.* `D5/S3/Weil/Pick/MassSupportKernelPencil.shiftedSupportWeightMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal of mass times support minus the pencil parameter.

**Definition 1.5 (Cauchy atom vector).**

Lean statement: `D5/S3/Weil/Pick/MassSupportKernelPencil.cauchyAtomVector`

*Formalization.* `D5/S3/Weil/Pick/MassSupportKernelPencil.cauchyAtomVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sampled Cauchy column associated with one support atom.

**Definition 1.6 (Cauchy dual certificate).**

Lean statement: `D5/S3/Weil/Pick/MassSupportKernelPencil.IsCauchyDual`

*Formalization.* `D5/S3/Weil/Pick/MassSupportKernelPencil.IsCauchyDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cauchy analysis of the sample vector is the coordinate vector at one atom.

**Definition 1.7 (Supported generalized eigenpair).**

Lean statement: `D5/S3/Weil/Pick/MassSupportKernelPencil.IsSupportedGeneralizedEigenpair`

*Formalization.* `D5/S3/Weil/Pick/MassSupportKernelPencil.IsSupportedGeneralizedEigenpair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A nonzero vector with nonzero mass action satisfying the relative Gram eigenrelation.

**Theorem 1.8 (The mass-support pencil factors through shifted atomic weights).**

$$\operatorname{P}\left(m, x, p, lambda\right) = \operatorname{C}\left(x, p\right) \cdot \operatorname{Dshift}\left(m, x, lambda\right) \cdot \operatorname{Cadjoint}\left(x, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/MassSupportKernelPencil.mass_support_kernel_pencil_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common Cauchy feature matrix remains fixed and only the atomic diagonal is shifted.

**Theorem 1.9 (A Cauchy-dual vector is nonzero).**

$$\operatorname{IsCauchyDual}\left(x, p, a, v\right) \Rightarrow v \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/MassSupportKernelPencil.cauchy_dual_vector_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Its analyzed coordinate at the selected atom is one.

**Theorem 1.10 (The mass Gram matrix selects the dual atom).**

$$\operatorname{IsCauchyDual}\left(x, p, a, v\right) \Rightarrow \operatorname{KmassV}\left(m, x, p, v\right) = \operatorname{mass}\left(m, a\right) \cdot \operatorname{cauchyColumn}\left(x, p, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/MassSupportKernelPencil.mass_gram_mulVec_of_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dual certificate collapses every atomic column except the selected one.

**Theorem 1.11 (The support Gram matrix selects the dual atom).**

$$\operatorname{IsCauchyDual}\left(x, p, a, v\right) \Rightarrow \operatorname{KsupportV}\left(m, x, p, v\right) = \operatorname{mass}\left(m, a\right) \cdot \operatorname{support}\left(x, a\right) \cdot \operatorname{cauchyColumn}\left(x, p, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/MassSupportKernelPencil.support_gram_mulVec_of_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same selected column now carries mass times support.

**Theorem 1.12 (A dual atom obeys the support eigenrelation).**

$$\operatorname{IsCauchyDual}\left(x, p, a, v\right) \Rightarrow \operatorname{KsupportV}\left(m, x, p, v\right) = \operatorname{support}\left(x, a\right) \cdot \operatorname{KmassV}\left(m, x, p, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/MassSupportKernelPencil.support_gram_eigenrelation_of_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support coordinate is the exact relative eigenvalue.

**Theorem 1.13 (The pencil annihilates the dual vector at the recovered support).**

$$\operatorname{IsCauchyDual}\left(x, p, a, v\right) \Rightarrow \operatorname{PsupportAV}\left(m, x, p, a, v\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/MassSupportKernelPencil.pencil_mulVec_at_support_of_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution of the atom's support coordinate cancels the two Gram actions.

**Theorem 1.14 (A nondegenerate dual has nonzero mass action).**

$$\operatorname{NondegenerateCauchyDual}\left(m, x, p, a, v\right) \Rightarrow \operatorname{KmassV}\left(m, x, p, v\right) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/MassSupportKernelPencil.mass_gram_mulVec_ne_zero_of_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero selected mass and one nonzero sampled feature exclude the zero action.

**Theorem 1.15 (The selected support is a generalized eigenvalue).**

$$\operatorname{NondegenerateCauchyDual}\left(m, x, p, a, v\right) \Rightarrow \operatorname{IsGeneralizedEigenpairAtSupport}\left(m, x, p, a, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/MassSupportKernelPencil.support_is_generalized_eigenvalue_of_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dual, mass, and sampled-feature hypotheses package a genuine supported generalized eigenpair.

## References

- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.IsCauchyDual`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.IsSupportedGeneralizedEigenpair`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.cauchyAtomVector`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.cauchy_dual_vector_ne_zero`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.massGramMatrix`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.massSupportKernelPencil`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.mass_gram_mulVec_ne_zero_of_dual`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.mass_gram_mulVec_of_dual`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.mass_support_kernel_pencil_factorization`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.pencil_mulVec_at_support_of_dual`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.shiftedSupportWeightMatrix`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.supportGramMatrix`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.support_gram_eigenrelation_of_dual`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.support_gram_mulVec_of_dual`
- Truth anchor: `D5/S3/Weil/Pick/MassSupportKernelPencil.support_is_generalized_eigenvalue_of_dual`
- Dependency: [D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization](FiniteLocalizedStieltjesKernelFactorization.md)
