# Horizon Effective Index

## Abstract

Effective Hankel defect indices obey positivity, product, sum, and boundary laws.

**Theorem 1.1 (Finite Hankel horizon effective index).**

$$\begin{gathered}(\forall n \in \mathbb{N}, H \in \mathbb{R}^{n \times n}, \operatorname{IsFiniteHankel}(H) \land \operatorname{IsStrictlyContractive}(H) \Rightarrow\\{}\operatorname{IsUnit}(\operatorname{horizonDefect}(H)) \land 0 < \operatorname{det}(\operatorname{horizonDefect}(H)) \land\\{}0 < \operatorname{horizonEffectiveIndex}(H) \land \operatorname{horizonEffectiveIndex}(H) = \prod_{i \in \operatorname{Fin}(n)} {1 - \operatorname{finiteSingularValue}(H, i)^{2}}^{-1} \land\\{}\operatorname{log}(\operatorname{horizonEffectiveIndex}(H)) = -\operatorname{log}(\operatorname{det}(\operatorname{horizonDefect}(H)))) \land\\{}(\forall m, n \in \mathbb{N}, H \in \mathbb{R}^{m \times m}, K \in \mathbb{R}^{n \times n}, \operatorname{horizonEffectiveIndex}(\operatorname{orthogonalSum}(H, K)) = \operatorname{horizonEffectiveIndex}(H) \times \operatorname{horizonEffectiveIndex}(K)) \land\\{}(\forall n \in \mathbb{N}, \operatorname{horizonEffectiveIndex}(0_{n \times n}) = 1) \land\\{}(\operatorname{Tendsto}((sigma \mapsto {1 - sigma^{2}}^{-1}), \operatorname{nhdsWithin}(1, \operatorname{Iio}(1)), atTop)) \land\\{}(\exists H \in \mathbb{R}^{1 \times 1}, \operatorname{IsFiniteHankel}(H) \land \operatorname{IsStrictlyContractive}(H) \land \operatorname{horizonEffectiveIndex}(H) = 1).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/HorizonEffectiveIndex.finite_hankel_horizon_effective_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite square real matrices model the finite-rank Hankel operators. Strict contraction is stated by requiring every spectrally defined singular value to be below one.

The characteristic polynomial of the Hermitian Gram matrix, evaluated at one, gives the singular-value product for the defect determinant. Positivity makes the defect invertible and proves the reciprocal determinant and logarithmic formulas.

Block determinants give orthogonal-sum multiplicativity, the zero matrix gives normalization and an explicit inhabited Hankel example, and the reciprocal singular factor tends to infinity at the contractive boundary.

The declaration formalizes only the effective information index. It does not claim that a Jones index has been constructed.

## References

- Truth anchor: `D5/S3/Weil/Pick/HorizonEffectiveIndex.finite_hankel_horizon_effective_index`
