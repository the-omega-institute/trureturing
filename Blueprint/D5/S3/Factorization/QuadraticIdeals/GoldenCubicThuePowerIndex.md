# Native Thue determinant and monogenic-order index

## Abstract

The native binary Thue value calculates an actual index of integer orders.

**Theorem 1.1 (The marked determinant is the signed binary cubic).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThuePowerIndex.native_power_index_det`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThuePowerIndex.native_power_index_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write tau as u alpha plus v beta. The multiplication table gives the last column of the change of basis from 1, alpha, beta to 1, tau, tau squared. Its determinant is the binary cubic itself with its original sign.

**Theorem 1.2 (The native generator has exact index twice the square-role prime).**

Lean statement: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThuePowerIndex.actual_factorization_power_index`

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThuePowerIndex.actual_factorization_power_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The oriented square and cube factors of the original Lucas equation select an integral tau in the actual splitting field. Its power triple has discriminant 324P to the fourth against field discriminant 81P squared. The additive quotient by the full monogenic order has cardinality 2P. The class-group and norm sieve are not asserted by this theorem.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThuePowerIndex.actual_factorization_power_index`
- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenCubicThuePowerIndex.native_power_index_det`
- Dependency: [D5/S3/Factorization/QuadraticIdeals/GoldenCubicThueMaximalOrder](GoldenCubicThueMaximalOrder.md)
