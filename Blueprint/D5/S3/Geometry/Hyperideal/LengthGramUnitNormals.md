# Unit Normals from the Inverse-Gram Dual Basis

## Abstract

Positive inverse-Gram diagonals normalize the dual vectors to unit Lorentz normals.

For a realizing matrix M of a positive six-length Gram matrix, the inverse-Gram dual vector at each coordinate has positive Lorentz square. Dividing by the positive square root of that square produces a unit normal. The realizing rows themselves are unit because the diagonal of the length Gram matrix is one.

**Theorem 1.1 (The normalized dual vector is unit).**

$$\forall l \in Length6,\; \forall M \in Mat4,\; \left(\forall i \in Fin4,\; \operatorname{lorentz}\left(\operatorname{row}\left(M, i\right), \operatorname{row}\left(M, i\right)\right) = \operatorname{entry}\left(\operatorname{lengthGram}\left(l\right), i, i\right)\right) \Rightarrow \left(\left(\forall k \in Fin6,\; \operatorname{l}\left(k\right) > 0\right) \Rightarrow \left(\operatorname{det}\left(\operatorname{lengthGram}\left(l\right)\right) < 0 \Rightarrow \left(\forall i \in Fin4,\; \operatorname{lorentz}\left(\operatorname{unitDualNormal}\left(\operatorname{lengthGram}\left(l\right), M, i\right), \operatorname{unitDualNormal}\left(\operatorname{lengthGram}\left(l\right), M, i\right)\right) = 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/LengthGramUnitNormals.dual_unit_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse-diagonal positivity theorem supplies a positive normalizing denominator. The inverse-Gram dual metric then reduces the Lorentz square to that denominator squared, and the finite bilinear expansion finishes the normalization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/LengthGramUnitNormals.dual_unit_normal`
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramDualMetric](LengthGramDualMetric.md)
- Dependency: [D5/S3/Geometry/Hyperideal/LengthGramInverseDiagonal](LengthGramInverseDiagonal.md)
