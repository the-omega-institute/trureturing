# Relative Quotient Decomposition

## Abstract

A closed inclusion splits its ambient subspace and identifies the relative quotient.

**Theorem 1.1 (A relative quotient is the orthogonal residual).**

$$\forall k: \operatorname{RCLike},\ \forall E: \operatorname{CompleteInnerProductSpace}_{k},\ \forall M, N: \operatorname{ClosedSubmodule}(k, E),\ M \subseteq N \Rightarrow \operatorname{IsCompl}(\operatorname{include}(M, N), \operatorname{include}(M, N)^{\perp}) \land\ \operatorname{Isometry}(\operatorname{relativeQuotientIsometry}(M, N)) \land \operatorname{Bijective}(\operatorname{relativeQuotientIsometry}(M, N)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RelativeQuotientDecomposition.relative_quotient_orthogonal_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M and N be closed subspaces of a complete real-or-complex inner-product space, with M contained in N. The copy of M inside N is constructed as the range of the induced isometric inclusion, and its orthogonal complement is therefore relative to N.

The first conjunct states that these two subspaces are complementary. The remaining conjuncts name the canonical quotient map and state that it is both an isometry and a bijection from N modulo M onto the relative orthogonal complement.

Repository search found and directly applies quotient_orthogonal_complement_isometry. Pinned Mathlib search found and reuses Submodule.isCompl_orthogonal and Submodule.quotientEquivOrthogonal. No exact theorem was found that packages both clauses for two named closed subspaces.

## References

- Truth anchor: `D5/S3/Quantum/Completion/RelativeQuotientDecomposition.relative_quotient_orthogonal_decomposition`
- Dependency: [D5/S3/Quantum/Algebra/QuotientOrthogonalComplement](../Algebra/QuotientOrthogonalComplement.md)
