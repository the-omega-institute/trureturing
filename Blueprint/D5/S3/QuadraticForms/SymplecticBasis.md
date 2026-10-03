# Finite-Dimensional Symplectic Basis

## Abstract

A finite-dimensional nondegenerate alternating form has a symplectic basis, including the zero space.

**Theorem 1.1 (Attributed Darboux basis construction).**

$$\forall K, V, B, \operatorname{Field}\left(K\right) \land \operatorname{FiniteDimensional}\left(K, V\right) \land \operatorname{IsAlt}\left(B\right) \land \operatorname{Nondegenerate}\left(B\right) \Rightarrow \exists n, e, \operatorname{IsSymplecticBasis}\left(B, e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SymplecticBasis.exists_isSymplecticBasis` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *Symplectic bases of alternating bilinear forms in CsdLean4*. URL: <https://github.com/zblore/csd-lean4/blob/39182b9e91a2791f5acb5ceaa2612ed71da921b5/CsdLean4/Mathlib/LinearAlgebra/BilinearForm/SymplecticBasis.lean>.

*Commentary.*

Over any field K, on any finite-dimensional additive K-module V, every nondegenerate alternating bilinear form B admits a basis indexed by Fin n plus Fin n for some natural n. The two halves pair internally to zero and across halves by the Kronecker delta, with B(p_i,q_i)=+1. Dimension zero is included.

The proof is an attributed bounded port of Zayn Blore's CsdLean4 construction at immutable revision 39182b9e91a2791f5acb5ceaa2612ed71da921b5. It extracts a symplectic plane, proves nondegeneracy on its orthogonal complement, and recurses by finite dimension. The auxiliary induction and index equivalence stay inside the existence proof.

For predictive symplectic completion, this supplies bases for im L and ker O when the alternating form restricted to each space is nondegenerate. It does not establish those nondegeneracy hypotheses, mixed-energy vanishing or positive Williamson blocks. Its positive cross-pairing convention is opposite to Mathlib's Matrix.J.

## References

- Truth anchor: `D5/S3/QuadraticForms/SymplecticBasis.exists_isSymplecticBasis`
