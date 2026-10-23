# Actual Saved Native Suppliers

## Abstract

The original retained suppliers and their actual saved parent determine the path inventories.

**Theorem 1.1 (Split the Exact Saved Q Opening into Three Paths).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; \forall A \in \mathrm{LabelList}\left(m\right),\; \forall u \in \mathrm{Label}\left(m\right),\; \left(\mathrm{Base}\left(frame\right) = \mathrm{Append}\left(A, \mathrm{Singleton}\left(u\right)\right) \land 3 \le \mathrm{Length}\left(A\right)\right) \Rightarrow \left(\forall parent \in \mathrm{OuterParentWitnessFor}\left(m, frame, A, u\right),\; \mathrm{SameQOpeningThreeFragments}\left(parent\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2QSourcePromotion.native_j2_same_q_three_fragments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every saved OuterParentWitnessFor W in the same range, use joint pieces 5, 4 and reversed 1 of its retained Q seed to recover the middle E2 path. The actual ordered special path in W is cut at the two new index-zero marked edges. The resulting three simple paths have endpoints R0 to new primary L0, new primary R0 to new opposite L0, and new opposite R0 to old L2. Their concatenated support equals W.special.path.support exactly. Re-inserting the two actual cut edges recovers its complete edge list, and omitting them is exactly the filtered edge list. The primary new frame is nextFrame(reverseSelected F), while the opposite is nextFrame F. This conclusion is about W.special.path, not a newly selected special child.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2QSourcePromotion.native_j2_same_q_three_fragments`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBaseSlicing](NativeActualQBaseSlicing.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SourcePromotion](NativeJ2SourcePromotion.md)
