# Dihedral permutations preserve the written level

## Abstract

A rotation or reflection preserves or exchanges the matching products, with a common orientation factor in the signed equation.

**Theorem 1.1 (Dihedral inclusion).**

$$\forall m : \mathbb{N}, \forall s : \operatorname{Perm}(\operatorname{Col}(m)), 2 \le m \implies \operatorname{Dihedral}(s) \implies \operatorname{PreservesLevel}(s)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiPreservation.dihedral_preservesLevel` (`✓ std3`). ∎

*Citation.* Yuta Kozaki and Saburo Kakei (2026). *Coxeter Group Symmetries of Frieze Patterns*. DOI: [10.48550/arXiv.2611.25785](https://doi.org/10.48550/arXiv.2611.25785). URL: <https://arxiv.org/abs/2611.25785v1>.

*Commentary.*

Kozaki and Kakei give the two dihedral generators, their level preservation and their normalized action in equations (42)–(44). For a rotation or reflection, cyclic transport preserves or exchanges the two parity classes of edges. Accounting for the reversed closing edge and the orientation of a reflection transfers equality of the products.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiPreservation.dihedral_preservesLevel`
- Dependency: [D5/S3/Geometry/KozakiKakeiCycle](KozakiKakeiCycle.md)
