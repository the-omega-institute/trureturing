# Pairing partition moments

## Abstract

Retained singleton-block moments equal the original distinct-index moments on uncovered labels.

Let k be any natural order and let D be pairing partition data: retained quotient blocks have one label and free blocks have two. Let the underlying index type be finite, let A be a commutative real algebra, let ell be any real linear functional on A, and let Y and the original label weights f be arbitrary. No centering, normalization, quadratic relation, positivity, or independence is needed.

**Definition 1.1 (Retained blocks and uncovered positions).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionMoments.pairingPartitionRetainedEquiv`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionMoments.pairingPartitionRetainedEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural k and D in PairingPartitionData(k), pairingPartitionRetainedEquiv(D) is an equivalence between the finite type of retained quotient blocks and the positions outside the support of pairingPartitionPairs(D). It sends a retained block B to B.out and sends an uncovered position i to its quotient class. The quotient representative law proves one inverse identity; uniqueness inside a singleton label fiber proves the other.

**Theorem 1.2 (Retained-block moments on the original labels).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionMoments.pairingPartition_retained_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionMoments.pairingPartition_retained_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, D, finite index type, commutative real algebra A, linear functional ell, family Y, and original weight family f, sum over injective assignments x from D.retained to the index type the product, over retained blocks B, of the product of f(i,x(B)) over all labels i in B, multiplied by ell of the product of Y(x(B)). This signed sum equals distinctIndexMoment of the original weights f restricted to the uncovered positions, enumerated by Fintype.equivFin of the complement of the pairing support. Each retained label fiber is the singleton containing B.out. Reindex the assignment and both products by the retained-block equivalence, then use the existing assignment_moment_reindex theorem to express the answer as the canonical ordered distinct-index moment. The absolute value is never moved inside the signed sum.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionMoments.pairingPartitionRetainedEquiv`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionMoments.pairingPartition_retained_moment`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionComponentFactor](CollisionComponentFactor.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingPartitionCorrespondence](PairingPartitionCorrespondence.md)
