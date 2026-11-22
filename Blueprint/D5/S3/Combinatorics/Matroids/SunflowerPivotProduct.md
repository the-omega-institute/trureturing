# The Product of Pivoted Form Modules

## Abstract

A new petal coefficient is independent of coefficients on disjoint petals of size at least two avoiding the pivot.

**Theorem 1.1 (The Product of Pivoted Form Modules).**

Lean statement: `D5/S3/Combinatorics/Matroids/SunflowerPivotProduct.sunflower_pivot_product`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SunflowerPivotProduct.sunflower_pivot_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use alternating forms in an integral basis indexed by a finite ordered set. Fix a pivot, a vector with positive integer weights, and an integer n. In the submodule killed by n and by insertion of the pivot and weighted vectors, impose coefficient conditions at disjoint petals of the form degree, which is at least two. Every petal avoids the pivot. The adapted basis preserves the pivot line and each coefficient kernel. Projection to the new petal sector commutes with both insertions and preserves n-torsion. Sector exchange identifies the unrestricted module times the jointly restricted module with the product for the prior and new conditions separately.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SunflowerPivotProduct.sunflower_pivot_product`
- Dependency: [D5/S3/Combinatorics/Matroids/SunflowerCircuitWeightBasis](SunflowerCircuitWeightBasis.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SupportedPivotProduct](SupportedPivotProduct.md)
