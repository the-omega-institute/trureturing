# The Residue Product for Private Pairs

## Abstract

A common pivot compares simultaneous restrictions for overlapping omissions.

**Theorem 1.1 (Adding an omission with private pairs).**

Lean statement: `D5/S3/Combinatorics/Matroids/PrivatePairCircuitResidueProduct.private_pair_residue_product`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PrivatePairCircuitResidueProduct.private_pair_residue_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite ordered ground set of size K and a rank r with 3 <= r < K. Take a family consisting of a fresh omission and finitely many prior omissions, all of the specified rank size and containing a common element. Each omission has two private elements. Consider four cores whose bases are exactly the rank-sized sets with neither, both, just the prior family, or just the fresh omission removed. Use the same surjection from a finite expanded ground set for the weights in all four cases. In difference coordinates at the common element each omitted basis imposes zero at its petal coefficient. The product of the uniform and jointly restricted weighted residue modules is integrally linearly isomorphic to the product of the two separately restricted modules.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PrivatePairCircuitResidueProduct.private_pair_residue_product`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitDifferenceBasis](CircuitDifferenceBasis.md)
- Dependency: [D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily](PrivatePairOmissionFamily.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates](SparsePavingCircuitCoordinates.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SupportedPivotProduct](SupportedPivotProduct.md)
