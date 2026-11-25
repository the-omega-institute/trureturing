# The signed four-column branch

## Abstract

At four columns the two signed evaluations of a pair indicator separate edges and diagonals directly.

**Theorem 1.1 (Four-column necessity).**

$$\forall s : \operatorname{Perm}(\operatorname{Col}(2)), \forall c : \mathbb{C}, \operatorname{rename}(s,F(2)) = C(c) \cdot F(2) \implies \operatorname{Dihedral}(s)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiFour.dihedral_of_scalar_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed quadratic evaluates to one on the indicator of an edge and minus two on the indicator of a diagonal. Among the images of the two edges incident with a fixed vertex, at least one is an edge. The scalar must be one, so every edge maps to an edge.

**Theorem 1.2 (Necessity on the whole size range).**

$$\forall m : \mathbb{N}, \forall s : \operatorname{Perm}(\operatorname{Col}(m)), 2 \le m \implies m \neq 3 \implies \operatorname{PreservesLevel}(s) \implies \operatorname{Dihedral}(s)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KozakiKakeiFour.dihedral_of_preservesLevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply scalar rigidity to the admissible constant matrices. Then use signed pair evaluations for m equal to two and recovery by support counts for every m at least four.

## References

- Truth anchor: `D5/S3/Geometry/KozakiKakeiFour.dihedral_of_preservesLevel`
- Truth anchor: `D5/S3/Geometry/KozakiKakeiFour.dihedral_of_scalar_four`
- Dependency: [D5/S3/Geometry/KozakiKakeiSupport](KozakiKakeiSupport.md)
