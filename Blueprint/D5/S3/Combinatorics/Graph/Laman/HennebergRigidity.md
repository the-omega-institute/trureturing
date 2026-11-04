# HennebergRigidity

## Abstract

Both geometric Henneberg moves in the real plane, with their exact hypotheses.

**Theorem 1.1 (A point outside a line).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.exists_not_mem_span_singleton_dim_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.exists_not_mem_span_singleton_dim_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every nonzero vector in the real plane, there exists a point outside its linear span. The span has dimension one, less than the ambient dimension two.

**Theorem 1.2 (Type I kernel injection).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeI_isInfinitesimallyRigid_extend`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeI_isInfinitesimallyRigid_extend` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Let V be finite, p a planar rigid placement of G, and a,b old vertices. If the displacement vectors q-p(a) and q-p(b) are linearly independent over the reals, then the placement on Option V sending none to q and some v to p(v) is rigid for typeI G a b. Restriction of velocities to old vertices is an injective map between the rigidity kernels.

**Theorem 1.3 (Avoiding a line and a finite set).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.exists_off_line_off_finite_dim_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.exists_off_line_off_finite_dim_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For any distinct real planar points pa,pb and any finite set S of planar points, there exists q outside S for which q-pa and q-pb are linearly independent. A finite union of proper affine subspaces cannot cover the plane.

**Theorem 1.4 (Type I preserves an injective rigid witness).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeI_isGenericallyRigidInj_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeI_isGenericallyRigidInj_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite vertex type, graph with an injective planar rigid placement, and distinct old vertices a,b, typeI G a b admits an injective planar rigid placement. Choose the new point outside the old placement image and the line through the attachments.

**Theorem 1.5 (Recovering the deleted-edge equation).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_collinear_inner_combo`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_collinear_inner_combo` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

In any natural dimension d and for any real s, assume q-p(a)=s times (p(b)-p(a)). For every velocity on Option V, (s-1) times the new a-edge inner product minus s times the new b-edge inner product equals s(s-1) times the old ab-edge inner product. The identity itself does not require s to avoid zero or one.

**Theorem 1.6 (Type II kernel injection).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_isInfinitesimallyRigid_extend`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_isInfinitesimallyRigid_extend` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Let V be finite and p a planar rigid placement of G. Suppose alpha is real, alpha!=0, alpha!=1, q-p(a)=alpha times (p(b)-p(a)), and q-p(a),q-p(c) are linearly independent. Then the Option placement extending p by q is rigid for typeII G a b c. The collinear identity recovers the removed ab equation, and the two independent displacements make restriction of kernel velocities injective. The theorem has no old-edge premise.

**Theorem 1.7 (Type II at a noncollinear placement).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_isGenericallyRigidInj_two_of_nonCollinear`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_isGenericallyRigidInj_two_of_nonCollinear` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite graph with an injective rigid planar placement p, if p(b)-p(a) and p(c)-p(a) are linearly independent, typeII G a b c admits an injective rigid planar placement. Choose q on the ab line away from the endpoints and the finite old placement image, retaining independence from the c displacement.

**Theorem 1.8 (A one-coordinate perturbation).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.exists_nonCollinear_update_perturbation_dim_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.exists_nonCollinear_update_perturbation_dim_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

Let V have decidable equality, pzero a planar placement, and a,b distinct from c. Assume pzero(b)-pzero(a) is nonzero and w lies outside its span. If a placement property P holds eventually as the c coordinate changes to pzero(c)+t times w near t=0, there exists a placement satisfying P with p(b)-p(a),p(c)-p(a) linearly independent. The statement imposes no finiteness hypothesis on V.

**Theorem 1.9 (Type II preserves an injective rigid witness).**

Lean statement: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_isGenericallyRigidInj_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_isGenericallyRigidInj_two` (`✓ std3`). ∎

*Citation.* Bryan Gin-ge Chen (2026). *CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578*. URL: <https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578>.

*Commentary.*

For every finite V, graph G admitting an injective planar rigid placement, and pairwise distinct old vertices a,b,c, typeII G a b c admits such a placement. Openness of rigidity and injectivity allows a noncollinear perturbation before the line construction. This geometric theorem does not require G.Adj a b. The combinatorial preservation theorem for Laman counts requires that old edge, and the reverse decomposition supplies it.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.exists_nonCollinear_update_perturbation_dim_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.exists_not_mem_span_singleton_dim_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.exists_off_line_off_finite_dim_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_collinear_inner_combo`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_isGenericallyRigidInj_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_isGenericallyRigidInj_two_of_nonCollinear`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeII_isInfinitesimallyRigid_extend`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeI_isGenericallyRigidInj_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.typeI_isInfinitesimallyRigid_extend`
- Dependency: [D5/S3/Combinatorics/Graph/Laman/Framework](Framework.md)
- Dependency: [D5/S3/Combinatorics/Graph/Laman/Moves](Moves.md)
