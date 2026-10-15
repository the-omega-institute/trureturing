# Actual Saved Native Suppliers

## Abstract

The original retained suppliers and their actual saved parent determine the path inventories.

**Theorem 1.1 (Earn the Eight Actual Third-Order Joint Pieces on the Same Parent).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; \forall A \in \mathrm{LabelList}\left(m\right),\; \forall u \in \mathrm{Label}\left(m\right),\; \left(\mathrm{Base}\left(frame\right) = \mathrm{Append}\left(A, \mathrm{Singleton}\left(u\right)\right) \land 3 \le \mathrm{Length}\left(A\right)\right) \Rightarrow \left(\forall parent \in \mathrm{OuterParentWitnessFor}\left(m, frame, A, u\right),\; \mathrm{SameParentEightPiecePartition}\left(parent\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2JointPromotion.native_j2_same_parent_eight_piece_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, every old two-label frame F with base A appended by u and A of length at least three, and every saved OuterParentWitnessFor W, construct eight genuine paths on its independently defined outer parent domain. Their order is reversed new piece 0, new piece 1, new piece 2, old P pieces 4, 3, 2, 0 and 5. For N0 = nextFrame(reverseSelected F) and N1 = nextFrame F, their oriented endpoints are respectively (L N0 0,L N0 2), (R N0 0,L N1 0), (R N1 0,L N1 1), (R N0 1,R N0 2), (L N1 3,R N0 3), (R N1 2,L N0 3), (R N1 1,R N1 3), and (L N1 2,L N0 1). Two disjoint actual cut sets map exactly to the marked cuts of N0 and N1. These pieces form ActualCyclePartition of the same W.cycle: their full support is a permutation of its tail support, their edges are a permutation of its edges outside the cut union, and every cut belongs to this cycle. No replacement parent or abstract target-partition certificate is assumed. The complete strong k3 state and all-size induction are further consumers; this theorem alone does not assert all-n Hamiltonicity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2JointPromotion.native_j2_same_parent_eight_piece_partition`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJointUpdate](NativeActualJointUpdate.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2QSourcePromotion](NativeJ2QSourcePromotion.md)
