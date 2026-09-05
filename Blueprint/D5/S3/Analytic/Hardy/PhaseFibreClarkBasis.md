# Phase-Fibre Clark Basis

## Abstract

A full-cardinality orthonormal phase fibre is an orthonormal basis of its finite-dimensional model space.

**Theorem 1.1 (The normalized phase fibre is a complete orthonormal basis).**

$$\begin{aligned}\operatorname{Orthonormal}(K, e) \land \operatorname{finrank}(K, H) = m \Rightarrow\\\exists b: \operatorname{OrthonormalBasis}(\operatorname{Fin}(m), K, H),\\\forall j \in \operatorname{Fin}(m), \operatorname{apply}(b, j) = \operatorname{apply}(e, j).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hardy/PhaseFibreClarkBasis.phase_fibre_is_orthonormal_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let e be the family of normalized boundary kernels indexed by the m points of one regular phase fibre. If the kernel identity makes this family orthonormal and the model space has dimension m, then e is the underlying family of an orthonormal basis.

The finite-dimensional assumption is explicit. A bare Lean finrank equality would not carry the source's dimension meaning in the zero-dimensional case unless finite dimensionality were already known.

Pinned Mathlib supplies the whole linear-algebraic step. Orthonormal.linearIndependent gives independence, LinearIndependent.span_eq_top_of_card_eq_finrank' upgrades the m vectors to a spanning family, and OrthonormalBasis.mk packages the resulting basis. The Blaschke boundary-cover construction, kernel orthogonality, and normalization identities remain separate analytic inputs.

## References

- Truth anchor: `D5/S3/Analytic/Hardy/PhaseFibreClarkBasis.phase_fibre_is_orthonormal_basis`
