# Products of Pivoted Coefficient Kernels

## Abstract

Supported changes of basis separate old and new coefficient conditions.

**Theorem 1.1 (The product identity in an adapted basis).**

Lean statement: `D5/S3/Combinatorics/Matroids/SupportedPivotProduct.pivot_product_of_supported_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SupportedPivotProduct.pivot_product_of_supported_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use alternating forms of degree d + 1 with values in an abelian group, over an integral basis indexed by a finite ordered set. Let K be the forms killed by an integer n and by insertion of the pivot and the weighted vector. Let P be the common kernel in K of a finite family of prior d + 1 element coefficients, and Q the kernel in K of the selected coefficient. Suppose an integral basis change preserves the pivot line and the spans of all these faces in both directions. The transformed weight vector has natural coefficients and vanishes on a set A that avoids the pivot. The selected face has a different intersection with A from every prior face. Then K times the intersection of P and Q is integrally linearly isomorphic to P times Q. The adapted projection preserves both insertion kernels and n-torsion.

**Theorem 1.2 (The product identity for faces with private pairs).**

Lean statement: `D5/S3/Combinatorics/Matroids/SupportedPivotProduct.private_pair_pivot_product`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SupportedPivotProduct.private_pair_pivot_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the same finite ordered integral basis, degree, coefficient group, pivot insertion, weighted insertion and n-torsion. Assume the original weights are positive integers, the selected face is distinct from every prior face, all faces avoid the pivot, and each has two indices in no other face. The adapted weight basis separates the selected coefficient and preserves the pivot and all face spans. Thus the same integral product isomorphism holds.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SupportedPivotProduct.pivot_product_of_supported_basis`
- Truth anchor: `D5/S3/Combinatorics/Matroids/SupportedPivotProduct.private_pair_pivot_product`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitCoefficientExchange](CircuitCoefficientExchange.md)
- Dependency: [D5/S3/Combinatorics/Matroids/PrivatePairCircuitWeightBasis](PrivatePairCircuitWeightBasis.md)
