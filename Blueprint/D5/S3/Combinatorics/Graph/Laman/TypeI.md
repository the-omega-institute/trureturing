# Type I and Type II geometric preservation

## Abstract

Real planar Henneberg rigidity preservation.

**Theorem 1.1 (A point outside a nonzero plane line).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_not_mem_span_singleton_dim_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_not_mem_span_singleton_dim_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A nonzero vector span in the real plane is proper, so a point outside it exists.

**Theorem 1.2 (Type I kernel injection).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isInfinitesimallyRigid_extend`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isInfinitesimallyRigid_extend` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

If a finite graph has an infinitesimally rigid planar placement and the new point has independent displacement vectors to two attachments, the Type I extension is infinitesimally rigid.

**Theorem 1.3 (An off-line point outside a finite set).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_off_line_off_finite_dim_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_off_line_off_finite_dim_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Given two distinct planar points and a finite set, there is a point outside that set with linearly independent displacement vectors to both points.

**Theorem 1.4 (Type I preserves injective generic rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isGenericallyRigidInj_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isGenericallyRigidInj_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Injective generic rigidity in the plane is preserved by a Type I Henneberg move at distinct attachments.

**Theorem 1.5 (The Type II deleted-edge identity).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_collinear_inner_combo`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_collinear_inner_combo` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

The collinear Type II placement identity recovers the deleted-edge rigidity equation from the two new-edge equations.

**Theorem 1.6 (Type II kernel injection).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_isInfinitesimallyRigid_extend`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_isInfinitesimallyRigid_extend` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A collinear Type II extension with an independent third displacement preserves infinitesimal rigidity in the plane.

**Theorem 1.7 (Conditional Type II generic rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_isGenericallyRigidInj_two_of_nonCollinear`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_isGenericallyRigidInj_two_of_nonCollinear` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A non-collinear injectively rigid planar placement yields an injectively rigid Type II extension.

**Theorem 1.8 (A non-collinear continuous perturbation).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_nonCollinear_update_perturbation_dim_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_nonCollinear_update_perturbation_dim_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

A continuous one-coordinate perturbation can make three planar placement points non-collinear while avoiding a finite set.

**Theorem 1.9 (Type II preserves injective generic rigidity).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_isGenericallyRigidInj_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_isGenericallyRigidInj_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Injective generic rigidity in the plane is preserved by every legal Type II Henneberg move.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_nonCollinear_update_perturbation_dim_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_not_mem_span_singleton_dim_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.exists_off_line_off_finite_dim_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_collinear_inner_combo`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_isGenericallyRigidInj_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_isGenericallyRigidInj_two_of_nonCollinear`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeII_isInfinitesimallyRigid_extend`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isGenericallyRigidInj_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/TypeI.typeI_isInfinitesimallyRigid_extend`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/Framework](Framework.md)
- Dependency: [D5/S3/Combinatorics/Graph/Laman/Moves](Moves.md)
