# LatticeHalfFockCollisionJacobi

## Abstract

Actual same-numerator nested current iterate

**Theorem 1.1 (Actual nested iterate from the three Taylor contractions).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionJacobi.actual_nested_iterate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionJacobi.actual_nested_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Fix arbitrary lattice data D with unit determinant, an actual current index i, original sources a,b and signed lifts and modes gamma,delta,d,r. K is an actual locality order of the entire A/B commutator. H1 is an independent locality order for Ad/B; H2(j) is an independent order for J/Q(A,B) over j<(K-r).toNat; H3(j) is an independent order for A/Bj over j<frequencyBound(b)+1. No locality of a Laurent monomial or of an ordered half is inferred.

The generic common-cleared-fields construction supplies a finite scalar homogeneous slice P of the actual JAB numerator at this same K. Every signed exponent satisfies the exact coefficient equation. No hidden existential cutoff is assumed to be valid. The existing FirstOuterTaylor, ABOuterTaylor and SecondSourceTaylor weighted identities all consume this very P.

The scalar identity fused(A,k)=ordered(k,-A-k-2)-epsilon(k)*ordered(k,A) uses the existing signed binomial kernel for k<0 and finite binomial symmetry for k>=0, including vanishing branches. Contracting this identity against the finite Taylor sum joins the three actual coefficient equalities. Linear functionals separate vectors and coefficients separate fields, giving the native nested iterate identity with its exact two finite ranges.

Negative degree, an empty range, zero states, rank zero, repeated sources, indefinite nondegenerate forms and all signed lifts remain in scope. This is a classical formal local-field calculation, using Matsuo--Nagatomo and Bakalov--Kac conventions and Mathlib algebra. It establishes a dependency of original-source compatibility; the full Monster, CFT, anomalies, fusion, string and AdS/CFT programme remains active.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockCollisionJacobi.actual_nested_iterate`
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor](LatticeHalfFockABOuterTaylor.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockFirstOuterTaylor](LatticeHalfFockFirstOuterTaylor.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor](LatticeHalfFockSecondSourceTaylor.md)
