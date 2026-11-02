# Type I geometric preservation

## Abstract

Real planar Type I Henneberg rigidity preservation.

**Theorem 1.1 (Type I kernel injection).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isInfinitesimallyRigid_extend`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isInfinitesimallyRigid_extend` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

If a finite graph has an infinitesimally rigid placement in the plane and the new point has linearly independent displacement vectors to two distinct attachment vertices, the Option extension is infinitesimally rigid. The proof injects the extended kernel into the old kernel by restriction to existing vertices.

**Theorem 1.2 (An off-line point outside a finite set).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_off_line_off_finite_dim_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_off_line_off_finite_dim_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Given two distinct points in the real plane and a finite set, there is a point outside that set whose displacement vectors to the two points are linearly independent.

**Theorem 1.3 (Type I preserves injective generic rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isGenericallyRigidInj_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isGenericallyRigidInj_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite graph, an injectively generically rigid planar placement remains injectively generically rigid after a Type I move at distinct attachment vertices. The new point is chosen off the old image and off the attachment line.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_off_line_off_finite_dim_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isGenericallyRigidInj_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isInfinitesimallyRigid_extend`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/Framework](Framework.md)
- Dependency: [D5/S3/Combinatorics/Graph/Laman/Moves](Moves.md)
