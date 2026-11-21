# Dihedral permutations preserve the written level

## Abstract

A rotation or reflection preserves or exchanges the matching products, with a common orientation factor in the signed equation.

**Theorem 1.1 (Dihedral inclusion).**

$$\forall m : \mathbb{N}, \forall s : \operatorname{Perm}(\operatorname{Col}(m)), 2 \le m \implies \operatorname{Dihedral}(s) \implies \operatorname{PreservesLevel}(s)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiPreservation.dihedral_preservesLevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cyclic transport preserves or exchanges the two parity classes of edges. Accounting for the reversed closing edge and the orientation of a reflection transfers equality of the products.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiPreservation.dihedral_preservesLevel`
- Dependency: [D5/S3/Geometry/KozakiKakeiCycle](KozakiKakeiCycle.md)
