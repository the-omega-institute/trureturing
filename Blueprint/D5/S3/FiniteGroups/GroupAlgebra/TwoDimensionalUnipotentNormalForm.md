# A basis for a faithful two-dimensional action

## Abstract

A faithful two-dimensional exponent-p action has an actual unitriangular basis over any field of characteristic p.

Let K be any field, p a prime with char K=p, and E a nontrivial additive commutative group such that p times e is zero for every e in E. Let V be a finite-dimensional K-vector space with finrank K V=2, and let rho be an injective representation of the additive group E, written as Multiplicative E, on V. K, E and V have independent universes; neither E nor K is required to be finite.

This is the classical two-dimensional unipotent normal form used by Elmer and Kadr, Some formulae relating modular representations of elementary abelian p-groups, arXiv:2510.07939v1, DOI 10.1007/s13366-026-00855-9. The proof below also permits infinite E. It supplies an actual basis and additive parameter for the later symmetric-power construction.

**Theorem 1.1 (The basis and faithful additive parameter).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/TwoDimensionalUnipotentNormalForm.exists_faithful_unipotent_basis`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/TwoDimensionalUnipotentNormalForm.exists_faithful_unipotent_basis` (`✓ std3`). ∎

*Citation.* Jonathan Elmer and Kazal Kadr (2025). *Some formulae relating modular representations of elementary abelian p-groups*. DOI: [10.1007/s13366-026-00855-9](https://doi.org/10.1007/s13366-026-00855-9). URL: <https://arxiv.org/html/2510.07939v1>.

*Commentary.*

For every K,p,E,V,rho as above, there exist a basis b indexed by Fin 2 and an injective additive homomorphism alpha:E->K such that, for every e in E, rho(e)(b(0))=b(0) and rho(e)(b(1))=alpha(e) times b(0)+b(1). The action notation rho(e) means rho(Multiplicative.ofAdd e). Faithfulness, the exponent-p law and dimension two are premises; the basis, both action equations and alpha are conclusions.

Choose a nonidentity displacement N=rho(e0)-id. The exponent-p law and the characteristic imply that each displacement is nilpotent; dimension two makes its square zero. Choose v with N(v) nonzero and set b(0)=N(v), b(1)=v. The commuting group action preserves N, which forces equal diagonal coordinates. Nilpotence of every displacement makes both diagonal coordinates one, including in characteristic two. The off-diagonal coordinates define alpha; the representation law gives additivity, and faithfulness gives injectivity.

No algebraic closure, chosen fixed vector, invariant complement, indecomposability assumption or restriction excluding p=2 is used. This module establishes the classical source reduction, and its actual consumer is the genuine quotient symmetric-power model in SymmetricPowerTranslation. It does not itself classify relative tensor products or settle the external conjectures.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/TwoDimensionalUnipotentNormalForm.exists_faithful_unipotent_basis`
