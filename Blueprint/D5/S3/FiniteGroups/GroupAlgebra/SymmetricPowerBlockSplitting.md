# Actual quotient splittings from dual tensor sections

## Abstract

Dual symmetric tensor multiplication and permutation averaging construct actual retractions on genuine symmetric quotients.

Let K be a field of type Type, E an additive group in an independent universe, and A and B vector spaces of type Type with E-actions rho and sigma. Write T_n(A) for the Fin n indexed tensor power with diagonal action, and q for Mathlib's actual quotient T_n(A)->SymmetricPower K (Fin n) A. The quotient helpers are reused from SymmetricPowerTranslation. The coefficient-ring universe restriction comes from this pinned quotient API, rather than a finiteness or characteristic assumption.

**Definition 1.1 (The actual dual multiplication inclusion).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.coefficientInclusion`

*Formalization.* `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.coefficientInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given a finite basis b of A and an equivariant map mu:T_n(A)->B, coefficientInclusion is the composite of the ordinary dual of mu, the inverse of the genuine finite tensor-dual equivalence, and the actual quotient T_n(A*)->Sym^n(A*). No symmetric-power duality equivalence is assumed. This definition alone asserts neither injectivity nor splitting.

**Theorem 1.2 (Averaging descends a tensor retraction).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.exists_coefficient_retraction`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.exists_coefficient_retraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose an equivariant s:B->T_n(A) satisfies mu s=id, mu is invariant under every actual permutation of tensor positions, and (n!:K) is nonzero. The theorem constructs an equivariant retraction of coefficientInclusion from the genuine Sym^n(A*) quotient to B*. Its composite with the inclusion is exactly id, with no stable equivalence or relative-projectivity substitution.

Dualizing the supplied tensor section gives a tensor retraction. Permutation invariance of mu makes its dual inclusion fixed under the actual factor permutations, proved through the tensor-dual pairing. Averaging the tensor retraction over all n! permutations gives a symmetric multilinear map and hence descends through the existing quotient universal property. Each summand has the same composite on the inclusion; division by n! gives the identity. These are the classical finite-group averaging and finite tensor-duality mechanisms. The tensor section is an explicit premise of this general helper; its construction for bounded polynomials is supplied by ElmerKadrSymmetricPowerSplitting.

**Theorem 1.3 (Ordered coefficient sums retain multiplicities).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.coefficientInclusion_basis`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.coefficientInclusion_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If mu sends each tensor-basis word indexed by t:Fin n->I to c(degree t), then coefficientInclusion sends c*(i) to the sum of the actual quotient classes of the dual words over every ordered t with degree t=i. Repeated quotient monomials remain repeated terms. This exact tensor-dual basis expansion proves the image identification used for the paper's coefficient-sum submodule, without assuming a monomial normalization or dividing by the degrees of the factors.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.coefficientInclusion`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.coefficientInclusion_basis`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerBlockSplitting.exists_coefficient_retraction`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/BoundedTensorPolarization](BoundedTensorPolarization.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/SymmetricPowerTranslation](SymmetricPowerTranslation.md)
