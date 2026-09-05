# Nilpotent Normality Obstruction

## Abstract

A nonzero nilpotent perturbation of a scalar cannot be normal or self-adjoint.

**Theorem 1.1 (A nonzero nilpotent scalar shift is not normal).**

$$\forall A, \operatorname{CStarAlgebra}\left(A\right) \Rightarrow\ \forall lambda \in \mathbb{C}, N \in A,\ (\operatorname{IsNilpotent}\left(N\right) \land N \neq 0) \Rightarrow\ \neg \operatorname{IsStarNormal}\left(lambda I + N\right) \land\ \neg \operatorname{IsSelfAdjoint}\left(lambda I + N\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/NilpotentNormalityObstruction.nonzero_nilpotent_shift_not_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a complex C-star algebra. If N is nonzero and nilpotent, then lambda times the identity plus N is not star-normal and therefore is not self-adjoint. Bounded operators for any chosen Hilbert-space inner product are a direct instance.

The source headline mentions an operator having a nontrivial Jordan block, but its proof additionally assumes that the operator has the single-eigenvalue form lambda I plus nilpotent N. The formal statement records that necessary hypothesis explicitly instead of inferring a unique eigenvalue from the presence of one block.

Pinned Mathlib has no packaged theorem saying that a normal nilpotent element vanishes. The proof combines spectralRadius_pow_le with IsStarNormal.spectralRadius_eq_nnnorm, then uses Commute.isStarNormal_sub to remove the scalar part. The final self-adjoint obstruction uses IsSelfAdjoint.isStarNormal.

## References

- Truth anchor: `D5/S1/Eigenstructure/NilpotentNormalityObstruction.nonzero_nilpotent_shift_not_normal`
