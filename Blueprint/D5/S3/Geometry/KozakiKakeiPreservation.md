# Dihedral permutations preserve the written level

## Abstract

A rotation or reflection preserves or exchanges the matching products, with a common orientation factor in the signed equation.

**Theorem 1.1 (Reversing an ordered minor).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPreservation.minor_swap`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiPreservation.minor_swap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exchanging the two arguments of a minor multiplies it by minus one.

**Theorem 1.2 (Dihedral inclusion).**

Lean statement: `D5/S3/Geometry/KozakiKakeiPreservation.dihedral_preservesLevel`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiPreservation.dihedral_preservesLevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cyclic transport preserves or exchanges the two parity classes of edges. Accounting for the reversed closing edge and the orientation of a reflection transfers equality of the products.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiPreservation.dihedral_preservesLevel`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiPreservation.minor_swap`
- Dependency: [D5/S3/Geometry/KozakiKakeiCycle](KozakiKakeiCycle.md)
