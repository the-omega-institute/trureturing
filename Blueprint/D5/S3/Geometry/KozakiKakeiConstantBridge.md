# From admissible constant matrices to a polynomial identity

## Abstract

The roots over distinct complex coordinates suffice to recover the signed matching polynomial up to a nonzero scalar.

**Theorem 1.1 (Nonzero signed polynomial).**

$$\forall m : \mathbb{N}, 2 \le m \implies m \neq 3 \implies F(m) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiConstantBridge.F_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first-coordinate coefficient is nonzero in each of the two size ranges.

**Theorem 1.2 (Scalar rigidity on the injective zero locus).**

$$\forall m : \mathbb{N}, \forall s : \operatorname{Perm}(\operatorname{Col}(m)), 2 \le m \implies m \neq 3 \implies (\forall t : \operatorname{Col}(m) \to \mathbb{C}, \operatorname{Injective}(t) \implies \operatorname{eval}(t,F(m))=0 \implies \operatorname{eval}(t,\operatorname{rename}(s,F(m)))=0) \implies (\exists c : \mathbb{C}, c \neq 0 \land \operatorname{rename}(s,F(m)) = C(c) \cdot F(m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiConstantBridge.affine_polynomial_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the linear root to remove the first coordinate wherever the coefficient and collision factors are nonzero. Polynomial evaluation then gives the cross-multiplied identity. Relative primeness gives polynomial divisibility, and equality of total degrees makes the quotient a nonzero scalar.

**Theorem 1.3 (The constant-matrix bridge).**

$$\forall m : \mathbb{N}, \forall s : \operatorname{Perm}(\operatorname{Col}(m)), 2 \le m \implies m \neq 3 \implies \operatorname{PreservesLevel}(s) \implies (\exists c : \mathbb{C}, c \neq 0 \land \operatorname{rename}(s,F(m)) = C(c) \cdot F(m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiConstantBridge.admissible_constant_matrix_scalar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Preservation on all admissible rational-function matrices yields the scalar identity by applying the affine zero-locus argument to the admissible constant matrices.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiConstantBridge.F_ne_zero`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiConstantBridge.admissible_constant_matrix_scalar`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiConstantBridge.affine_polynomial_scalar`
- Dependency: [D5/S3/Geometry/KozakiKakeiPrimitive](KozakiKakeiPrimitive.md)
