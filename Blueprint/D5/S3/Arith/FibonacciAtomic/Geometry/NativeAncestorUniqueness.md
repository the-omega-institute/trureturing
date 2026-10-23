# Native Tree Uniqueness from Ancestor Coordinates

## Abstract

The full ordered leaf word and the exact inorder ancestor-area vector determine the native labelled tree.

**Theorem 1.1 (Equality of the Two Observations Forces Tree Equality).**

$$\forall s: \operatorname{Source}, (\forall t: \operatorname{Source}, ((\operatorname{wd}\left(s\right) = \operatorname{wd}\left(t\right)) \implies ((\operatorname{coordinates}\left(s\right) = \operatorname{coordinates}\left(t\right)) \implies (s = t))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness.native_ancestor_uniqueness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source is FreeMagma Bool: all nonempty finite ordered full binary trees with Boolean leaf labels. The word wd lists every label in left-to-right order. The ancestor coordinate list has one entry at each leaf gap, namely the product of the left and right child leaf counts at that gap's common ancestor. Its order is the left-child coordinates, the root product, and the right-child coordinates.

For any two actual sources s and t, equality of their full words and equality of their exact natural coordinate lists imply s=t as labelled ordered trees. Both labels, repeated labels, and repeated equal subtrees at different addresses remain in the domain. A singleton tree has an empty coordinate list; its word still identifies its label. There is no empty native tree.

The complete-interval criterion identifies every subtree interval from consecutive coordinate sums. In a paired tree, any complete prefix that is shorter than the whole tree lies inside the left child: its address is nonempty, and a right step would give a positive offset. The left child's full leaf interval is itself such a prefix. Transfer that interval between the two trees using coordinate equality. Each left-child size is at most the other's, so their root split positions agree.

The common split separates the words into the two child words. It also separates the coordinate lists: the left child has length(left)-1 gaps, then comes the root gap, then the right child. Hence both child pairs have equal words and equal coordinate lists. Structural induction identifies each child and therefore the entire native tree. Leaf cases use the complete ordered word directly.

This is an exact uniqueness statement about the specified observations. It supplies no observation-acquisition procedure, decoder, resource estimate, or finite-precision stability bound. Coordinates depend on actual ancestor relations; equality does not make them obtainable from the leaf word alone.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness.native_ancestor_uniqueness`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval](AncestorAreaInterval.md)
- Dependency: [D5/S3/Combinatorics/Partitions/WordPartitionInverse](../../../Combinatorics/Partitions/WordPartitionInverse.md)
