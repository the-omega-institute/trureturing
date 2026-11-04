# Duality

## Abstract

The Arakelov height of a subspace agrees with that of its dual annihilator.

**Definition 1.1 (Selected columns followed by their complement).**

Lean statement: `D5/S3/Arith/AbsoluteValues/Heights/Duality.enumEquiv`

*Formalization.* `D5/S3/Arith/AbsoluteValues/Heights/Duality.enumEquiv` (`✓ std3`).

*Citation.* Ralf Stephan (2026). *Subspace-Theorems*. URL: <https://github.com/rwst/Subspace-Theorems/tree/bfd830f481b296989fa5f0c1e48d9316f72270d8>.

*Commentary.*

For a finite linearly ordered type and a subset s of cardinality k with complement of cardinality l, enumEquiv identifies Fin k plus Fin l with the original index type. It lists s in increasing order, followed by its complement in increasing order. The exact index identification is consumed by the metallic shifted complementary-minor proof.

**Theorem 1.2 (Complementary minors for dual block rows).**

Lean statement: `D5/S3/Arith/AbsoluteValues/Heights/Duality.det_submatrix_inl_eq_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/AbsoluteValues/Heights/Duality.det_submatrix_inl_eq_mul` (`✓ std3`). ∎

*Citation.* Ralf Stephan (2026). *Subspace-Theorems*. URL: <https://github.com/rwst/Subspace-Theorems/tree/bfd830f481b296989fa5f0c1e48d9316f72270d8>.

*Commentary.*

Let C and D be matrices over a commutative ring, with row type Fin k plus Fin l and finite ordered column type, satisfying C times transpose D equal to the identity. For a column subset s with cardinality k and complement of cardinality l, the determinant of the first block of C restricted to increasing s equals the determinant of C with its columns read through enumEquiv, multiplied by the determinant of the second block of D restricted to the increasing complement. This is the original duality declaration; the shifted Hankel boundary proof consumes it with an invertible enclosing matrix and its inverse transpose.

**Theorem 1.3 (Duality).**

Lean statement: `D5/S3/Arith/AbsoluteValues/Heights/Duality.arakelovMulHeight_comap_piEquiv_dualAnnihilator`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/AbsoluteValues/Heights/Duality.arakelovMulHeight_comap_piEquiv_dualAnnihilator` (`✓ std3`). ∎

*Citation.* Ralf Stephan (2026). *Subspace-Theorems*. URL: <https://github.com/rwst/Subspace-Theorems/tree/bfd830f481b296989fa5f0c1e48d9316f72270d8>.

*Commentary.*

The Arakelov height of a subspace agrees with that of its dual annihilator.

## References

- Truth anchor: `D5/S3/Arith/AbsoluteValues/Heights/Duality.arakelovMulHeight_comap_piEquiv_dualAnnihilator`
- Truth anchor: `D5/S3/Arith/AbsoluteValues/Heights/Duality.det_submatrix_inl_eq_mul`
- Truth anchor: `D5/S3/Arith/AbsoluteValues/Heights/Duality.enumEquiv`
- Dependency: [D5/S3/Arith/AbsoluteValues/Heights/PseudoBasis](PseudoBasis.md)
- Dependency: [D5/S3/Arith/AbsoluteValues/Heights/PseudoBasisMetrics](PseudoBasisMetrics.md)
