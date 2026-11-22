# Positive filters for prescribed conjugate modes

## Abstract

Positive filters for prescribed conjugate modes

**Theorem 1.1 (A positive measure can annihilate a conjugate pair and preserve a distinct mode).**

Lean statement: `D5/S3/Analytic/Asymptotics/ThreeAtomZeroFilter.exists_threeAtom_zero_filter`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/ThreeAtomZeroFilter.exists_threeAtom_zero_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose three positive masses at 0, a and 2a. The exponential transform factors into two linear factors in the exponential variable. Avoid the countable set of spacings where either factor would vanish at the protected mode.

**Theorem 1.2 (A compact probability for summably sparse selected modes).**

Lean statement: `D5/S3/Analytic/Asymptotics/ThreeAtomZeroFilter.exists_selective_spectral_filter`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/ThreeAtomZeroFilter.exists_selective_spectral_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the three-atom factors at the selected indices and point masses at zero at the other indices. Summability of the reciprocal positive ordinates bounds the total support length. The product vanishes at each selected conjugate pair and remains nonzero at the protected mode.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/ThreeAtomZeroFilter.exists_selective_spectral_filter`
- Truth anchor: `D5/S3/Analytic/Asymptotics/ThreeAtomZeroFilter.exists_threeAtom_zero_filter`
- Dependency: [D5/S3/Analytic/Asymptotics/PositiveSpectralKernel](PositiveSpectralKernel.md)
