# CubicThetaJacobiColumns

## Abstract

Every Laurent column of the actual Jacobi cube is obtained from a complete integer-pair lattice sum. The index-zero column is the norm theta series; no product-to-core identity is assumed.

Every Laurent column of the actual Jacobi cube is obtained from a complete integer-pair lattice sum. The index-zero column is the norm theta series; no product-to-core identity is assumed.

**Definition 1.1 (cubeColumn).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.cubeColumn`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.cubeColumn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The exact Laurent coefficient column of the actual normalized Jacobi cube.

**Theorem 1.2 (hasSum_cube_column).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.hasSum_cube_column`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.hasSum_cube_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

Each Laurent column of the genuine cube is the full sum over two free integers.

**Theorem 1.3 (triangular_zero_sum).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.triangular_zero_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.triangular_zero_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The zero-total triangular exponent is exactly Q(x,y).

**Theorem 1.4 (triangular_one_sum).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.triangular_one_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.triangular_one_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The one-total triangular exponent is exactly Q(x,y)-x-y.

**Theorem 1.5 (cube_column_zero).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.cube_column_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.cube_column_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The index-zero column of the actual Jacobi cube is the complete norm theta.

**Theorem 1.6 (cube_column_one).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.cube_column_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.cube_column_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The index-one column includes all three affine cosets, with the exact negative sign.

**Theorem 1.7 (signs_add).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.signs_add`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.signs_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Zeyu Huang, Timothy Huber, James McLaughlin, Pengjun Wang, Yan Xu and Dongxi Ye (2025). *Sign-patterns of Certain Infinite Products*. DOI: [10.48550/arXiv.2507.16644](https://doi.org/10.48550/arXiv.2507.16644). URL: <https://arxiv.org/abs/2507.16644v1>.

*Commentary.*

The three triangular monomial signs multiply to the sign of their full integer index sum.

This classical intermediate supplies complete Jacobi columns. CubicThetaCoreProduct and CubicThetaIdentities prove the downstream product-to-lattice identities; EtaSignK6 proves the exact all-index sign theorem. Independent formal acceptance and publication remain separate.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.cubeColumn`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.cube_column_one`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.cube_column_zero`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.hasSum_cube_column`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.signs_add`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.triangular_one_sum`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.triangular_zero_sum`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaJacobiCube](CubicThetaJacobiCube.md)
