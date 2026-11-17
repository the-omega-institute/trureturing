# Genuine symmetric powers in translation coordinates

## Abstract

Actual quotient symmetric powers and their contragredients acquire polynomial translation coordinates in every degree.

Let K be a field, V a K-vector space with a basis b indexed by Fin 2, and n a natural number. The source is the actual Mathlib quotient SymmetricPower K (Fin n) V. Its map to K[z] sends a pure tensor of vectors v_j to the product of the linear polynomials whose coordinates send b(0) to 1 and b(1) to z. The image lies in degree less than n+1.

The current Mathlib quotient shares its coefficient-ring and index universes: the literal index Fin n therefore requires K : Type here. V and the additive group E keep independent universes. This API boundary is explicit; it is not a finite-field, factorial, characteristic or degree restriction.

**Definition 1.1 (The actual quotient and bounded polynomials).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation.polynomialEquiv`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation.polynomialEquiv` (`✓ std3`).

*Citation.* Jonathan Elmer and Kazal Kadr (2025). *Some formulae relating modular representations of elementary abelian p-groups*. DOI: [10.1007/s13366-026-00855-9](https://doi.org/10.1007/s13366-026-00855-9). URL: <https://arxiv.org/html/2510.07939v1>.

*Commentary.*

For every basis b and natural n, polynomialEquiv is a K-linear equivalence from SymmetricPower K (Fin n) V to the polynomials of degree less than n+1. No averaging or division by n! is used. The result includes n=0 and n greater than or equal to the characteristic.

The construction descends the symmetric multilinear product through the actual additive-congruence quotient. Basis tensors span the quotient. Two words in the two basis vectors with the same number of occurrences of b(1) are related by an actual permutation of Fin n and hence have the same quotient class. The inverse sends the monomial z^i to a representative word with i occurrences of b(1). The two composites are proved to be identities.

**Theorem 1.2 (One parameter for every actual symmetric power and dual).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation.exists_faithful_polynomial_models`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation.exists_faithful_polynomial_models` (`✓ std3`). ∎

*Citation.* Jonathan Elmer and Kazal Kadr (2025). *Some formulae relating modular representations of elementary abelian p-groups*. DOI: [10.1007/s13366-026-00855-9](https://doi.org/10.1007/s13366-026-00855-9). URL: <https://arxiv.org/html/2510.07939v1>.

*Commentary.*

Now let E be a nontrivial additive commutative group of exponent p, where p is prime and char K=p. Let V have finrank two and let rho be an injective representation of Multiplicative E on V. There exists one injective additive alpha:E->K such that, for every natural n, both the actual degree-n symmetric-power representation and its ordinary contragredient are equivariantly isomorphic to the primal and dual polynomial translation models of dimension n+1 restricted along alpha.

The theorem obtains b and both action equations from exists_faithful_unipotent_basis. Its caller supplies no basis, alpha, polynomial-coordinate equation or desired equivalence. Equivariance of the primal quotient map follows on pure tensors and then on their span. For the contragredient, pull back by the inverse primal equivalence and use the inverse group element: the resulting dual action evaluates a polynomial at z-alpha(e). This fixes the sign without imposing a separate dual-action hypothesis.

At every positive original index i, the original dual module is the dual of SymmetricPower K (Fin (i-1)) V. Thus Sym^0 occurs at i=1; it is not the zero module V_0 of the polynomial extension. OriginalWClassification consumes the actual positive-index equivalences for its literal direct sums and tensors. The construction is the classical coordinate model underlying Elmer--Kadr Section 2.2, not a novelty or full open-problem resolution claim.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation.exists_faithful_polynomial_models`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation.polynomialEquiv`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorCounterexample](ElmerKadrTensorCounterexample.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/TwoDimensionalUnipotentNormalForm](TwoDimensionalUnipotentNormalForm.md)
