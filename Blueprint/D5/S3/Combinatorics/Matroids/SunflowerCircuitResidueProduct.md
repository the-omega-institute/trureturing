# The Sunflower Residue Product

## Abstract

The uniform, previously punctured, singly punctured and jointly punctured cores share a common coordinate model.

**Theorem 1.1 (The Sunflower Residue Product).**

Lean statement: `D5/S3/Combinatorics/Matroids/SunflowerCircuitResidueProduct.sunflower_residue_product`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SunflowerCircuitResidueProduct.sunflower_residue_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a rank of at least three below the ground size, and use cores on the same finite ordered ground set. Their bases are the rank-sized sets after the respective omissions. The prior omissions and the new omission all contain a common element and their petals are pairwise disjoint. A surjection from the finite expanded ground set gives the weights. Use the common element as the pivot. Each omission imposes the vanishing of its petal coefficient in difference coordinates. Sector exchange identifies the integral product of the uniform and jointly punctured residue modules with the product of the two separately punctured modules.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SunflowerCircuitResidueProduct.sunflower_residue_product`
- Dependency: [D5/S3/Combinatorics/Matroids/PrivatePairCircuitResidueProduct](PrivatePairCircuitResidueProduct.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SunflowerPivotProduct](SunflowerPivotProduct.md)
