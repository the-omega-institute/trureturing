# Residue Product for Separated Petals

## Abstract

The coefficient exchange product at a common pivot.

**Theorem 1.1 (Exchange of separated coefficients).**

Lean statement: `D5/S3/Combinatorics/Matroids/MembershipCircuitResidueProduct.membership_residue_product`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/MembershipCircuitResidueProduct.membership_residue_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let an omitted family consist of a previous family and one new member. All omissions have the same size and contain a common pivot. Suppose each pair differs on a membership class of size at least two. In the associated parallel expansions, the product of the uniform and joint residue modules is integrally linearly equivalent to the product of the previous and single-omission residue modules. The basis concentrates weights within classes and separates the coefficient of the new petal from those of the previous petals.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/MembershipCircuitResidueProduct.membership_residue_product`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis](CircuitDifferenceBasis.md)
- Dependency: [D5/S3/Combinatorics/Matroids/MembershipCircuitWeightBasis](MembershipCircuitWeightBasis.md)
- Dependency: [D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions](MembershipSeparatedOmissions.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates](SparsePavingCircuitCoordinates.md)
