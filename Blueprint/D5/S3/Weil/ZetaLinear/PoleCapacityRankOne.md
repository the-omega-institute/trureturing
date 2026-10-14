# Pole Capacity Rank One

## Abstract

A positive rank-one pole update removes at most one negative direction.

**Theorem 1.1 (A pole pair has negative-index capacity one).**

$$\forall I \in \operatorname{Type}\left(\right), F0 \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right), p \in I \to \mathbb{C},\; \left(\operatorname{Fintype}\left(I\right) \land \left(\operatorname{DecidableEq}\left(I\right) \land \operatorname{Hermitian}\left(F0\right)\right)\right) \Rightarrow \left(\operatorname{negIndex}\left(F0\right) - 1 \le \operatorname{negIndex}\left(F0 + 2 \cdot \operatorname{vecMulVec}\left(p, \operatorname{star}\left(p\right)\right)\right) \land \left(\operatorname{PosSemidef}\left(F0 + 2 \cdot \operatorname{vecMulVec}\left(p, \operatorname{star}\left(p\right)\right)\right) \Rightarrow \operatorname{negIndex}\left(F0\right) \le 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.pole_capacity_rank_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be a finite carrier with decidable equality, let F0 be a Hermitian complex matrix on I, and let p be a complex vector. The updated matrix is constructed as F0 plus twice the canonical outer product of p with its conjugate.

The negative spectral index of the update is at least the original negative index minus one. If the updated matrix is positive semidefinite, the original negative index is therefore at most one.

The proof applies negative-index subadditivity to the updated matrix and the negative rank-one correction. Pinned Mathlib supplies the outer-product positivity and rank bound; repository searches found no theorem already stating both public clauses.

**Theorem 1.2 (rank hermNegPart eq negIndex).**

$$\forall (K n : Type) [RCLike K] [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A . IsHermitian) , (RHLinalg . hermNegPart hA) . rank = RHLinalg . negIndex hA$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.rank_hermNegPart_eq_negIndex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative spectral part has rank equal to the number of negative eigenvalues.

**Theorem 1.3 (negDefOn range hermNegPart).**

$$\forall (K n : Type) [RCLike K] [Fintype n] [DecidableEq n] (A : Matrix n n K) (hA : A . IsHermitian) , RHLinalg . PosDefOn (- A) (LinearMap . range (RHLinalg . hermNegPart hA) . mulVecLin)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.negDefOn_range_hermNegPart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative of a Hermitian matrix is positive definite on the range of its negative spectral part.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.negDefOn_range_hermNegPart`
- Truth anchor: `D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.pole_capacity_rank_one`
- Truth anchor: `D5/S3/Weil/ZetaLinear/PoleCapacityRankOne.rank_hermNegPart_eq_negIndex`
