# Merged label moment bounds

## Abstract

Low-order disjoint-label estimates for merged component moments.

Let D be a finite index type, A a commutative real algebra, ell a real linear functional, and Y a family in A. An original family of k scalar weights is indexed by Fin k. Merging blocks multiplies all weights whose labels lie in the same component. Distinct components have disjoint label fibers, and every quotient component has a nonempty label fiber.

**Definition 1.1 (Uniform low-order hypothesis).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MergedLabelMomentBounds.DisjointLabelMomentBound`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MergedLabelMomentBounds.DisjointLabelMomentBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real C and s, the disjoint-label moment bound says that for every order r with 2<=r<k and every family of r nonempty pairwise disjoint subsets of Fin k, the absolute value of the ordered distinct-index moment of their product weights is at most C*s^r.

**Theorem 1.2 (Merged weights satisfy the component estimate).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MergedLabelMomentBounds.quotient_merged_assignment_abs_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MergedLabelMomentBounds.quotient_merged_assignment_abs_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let sigma partition Fin k and let tau partition the sigma-blocks. Let S be a retained set of sigma-blocks with card(S)<k. Assume C>=1, H>=1, s>=0, ell(1)=1, ell(Y(d))=0 for every d, card(D)<=C*H, and every original weight has absolute value at most one. Assume the disjoint-label moment bound and that the number of tau-components outside the image of S is at most q. Then the absolute value of the sum over sigma-block assignments that are constant on each tau-component and injective on S, of the product of all block weights times ell of the retained Y product, is at most C^(q+1)*H^q*s^card(S). A nested component weight is the product of the original weights over the fiber of the composite quotient map. Surjectivity makes each fiber nonempty, and different components give disjoint fibers. The assumed low-order estimate applies when there are at least two retained components; normalization and centering handle orders zero and one. The signed component factorization then gives the estimate without moving absolute values inside the retained moment sum.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MergedLabelMomentBounds.DisjointLabelMomentBound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MergedLabelMomentBounds.quotient_merged_assignment_abs_le`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionComponentFactor](CollisionComponentFactor.md)
