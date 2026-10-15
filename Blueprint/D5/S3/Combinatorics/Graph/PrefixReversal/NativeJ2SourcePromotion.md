# Actual Saved Native Suppliers

## Abstract

The original retained suppliers and their actual saved parent determine the path inventories.

**Theorem 1.1 (The Original P Opening Keeps Its Actual Joint Inventory).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; \forall A \in \mathrm{LabelList}\left(m\right),\; \forall u \in \mathrm{Label}\left(m\right),\; \left(\mathrm{Base}\left(frame\right) = \mathrm{Append}\left(A, \mathrm{Singleton}\left(u\right)\right) \land 3 \le \mathrm{Length}\left(A\right)\right) \Rightarrow \left(\forall parent \in \mathrm{OuterParentWitnessFor}\left(m, frame, A, u\right),\; \mathrm{OriginalPOpeningInventory}\left(parent\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SourcePromotion.native_j2_original_p_opening_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, every two-label frame F with base A appended by u and A of length at least three, and every saved OuterParentWitnessFor W, the final ordinary opening of W has precisely the full joint support of W.P. Its edges are a permutation of the same retained P cycle after removing the literal supplier cut at the outer final base gap. Restoring the two original marked groups before filtering gives the same remaining-edge inventory. Neither the original P supplier nor the assembled parent cycle is replaced.

**Theorem 1.2 (Earn the Actual Original P Prefix and Remaining Edges).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; \forall A \in \mathrm{LabelList}\left(m\right),\; \forall u \in \mathrm{Label}\left(m\right),\; \left(\mathrm{Base}\left(frame\right) = \mathrm{Append}\left(A, \mathrm{Singleton}\left(u\right)\right) \land 3 \le \mathrm{Length}\left(A\right)\right) \Rightarrow \left(\forall parent \in \mathrm{OuterParentWitnessFor}\left(m, frame, A, u\right),\; \mathrm{OriginalPJointPrefixSplit}\left(parent\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SourcePromotion.native_j2_original_p_joint_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same W, joint piece 1 of the original P seed begins with an actual a edge and then the particular b edge deleted by its final-child opening. Their intermediate vertices are exactly the right and left outer ports at index m minus one. The remaining tail is an actual path. The final opening support is a permutation of this distinguished joint path and the other five saved joint paths; its remaining edges are those of the other paths, the tail, the first a edge, and both original marked groups. This inventory is consumed by NativeJ2JointPromotion for this same W.cycle, rather than frozen merely as a record of an application.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SourcePromotion.native_j2_original_p_joint_split`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SourcePromotion.native_j2_original_p_opening_inventory`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualPJointPrefix](NativeActualPJointPrefix.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentWitnesses](NativeJ2ParentWitnesses.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory](../Walks/ActualJointHalfCutInventory.md)
