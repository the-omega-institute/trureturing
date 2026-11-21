# From admissible constant matrices to a polynomial identity

## Abstract

The roots over distinct complex coordinates suffice to recover the signed matching polynomial up to a nonzero scalar.

**Theorem 1.1 (Nonzero signed polynomial).**

Lean statement: `D5/S3/Geometry/KozakiKakeiConstantBridge.F_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiConstantBridge.F_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first-coordinate coefficient is nonzero in each of the two size ranges.

**Theorem 1.2 (Scalar rigidity on the injective zero locus).**

Lean statement: `D5/S3/Geometry/KozakiKakeiConstantBridge.affine_polynomial_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiConstantBridge.affine_polynomial_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the linear root to remove the first coordinate wherever the coefficient and collision factors are nonzero. Polynomial evaluation then gives the cross-multiplied identity. Relative primeness gives polynomial divisibility, and equality of total degrees makes the quotient a nonzero scalar.

**Theorem 1.3 (The constant-matrix bridge).**

Lean statement: `D5/S3/Geometry/KozakiKakeiConstantBridge.admissible_constant_matrix_scalar`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiConstantBridge.admissible_constant_matrix_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Preservation on all admissible rational-function matrices yields the scalar identity by applying the affine zero-locus argument to the admissible constant matrices.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiConstantBridge.F_ne_zero`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiConstantBridge.admissible_constant_matrix_scalar`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiConstantBridge.affine_polynomial_scalar`
- Dependency: [D5/S3/Geometry/KozakiKakeiPrimitive](KozakiKakeiPrimitive.md)
