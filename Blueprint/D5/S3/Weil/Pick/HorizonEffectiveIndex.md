# Horizon Effective Index

## Abstract

Effective Hankel defect indices obey positivity, product, sum, and boundary laws.

**Theorem 1.1 (Finite Hankel horizon effective index).**

Lean statement: `D5/S3/Weil/Pick/HorizonEffectiveIndex.finite_hankel_horizon_effective_index`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/HorizonEffectiveIndex.finite_hankel_horizon_effective_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite square real matrices model the finite-rank Hankel operators. Strict contraction is stated by requiring every spectrally defined singular value to be below one.

The characteristic polynomial of the Hermitian Gram matrix, evaluated at one, gives the singular-value product for the defect determinant. Positivity makes the defect invertible and proves the reciprocal determinant and logarithmic formulas.

Block determinants give orthogonal-sum multiplicativity, the zero matrix gives normalization and an explicit inhabited Hankel example, and the reciprocal singular factor tends to infinity at the contractive boundary.

The declaration formalizes only the effective information index. It does not claim that a Jones index has been constructed.

## References

- Truth anchor: `D5/S3/Weil/Pick/HorizonEffectiveIndex.finite_hankel_horizon_effective_index`
