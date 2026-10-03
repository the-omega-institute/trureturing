# Union Conditioning on One Common Regular Subtree

## Abstract

A uniform regular subtree obeys a height-independent lower bound for hitting an arbitrary leaf set after conditioning on a surviving prefix.

**Theorem 1.1 (A surviving prefix retains a fixed fraction of every leaf-union probability).**

Lean statement: `D5/S3/Arith/Congruence/ConditionalComparison/CommonTreeUnion.union_conditioning`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ConditionalComparison/CommonTreeUnion.union_conditioning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix integers 2 <= r < s and any finite height B. At every internal node of the full s-ary tree, choose a uniform r-element subset of its children, independently of all other nodes. A leaf is selected when every edge of its root path belongs to the corresponding chosen subset. All events use this one finite probability law, including choices at nodes that the selected subtree does not reach.

Let A be the event that some selected leaf extends a specified prefix of any depth d <= B, and let H be the event that a selected leaf belongs to any specified leaf set F. The theorem proves r(s-1) P(A and H) >= s(r-1) P(A) P(H). The coefficient is independent of B and d; the empty prefix, height zero and empty leaf set are included.

Uniformly deleting one element of a uniform r-element subset produces a uniform (r-1)-element subset. If the original subset hits a fixed set, at least r-1 deletion choices preserve that hit. Averaging this comparison over the actual child subtrees controls the union of hits in all children other than the specified prefix child.

Induction on the height combines this deletion comparison with the root selection law and independence of distinct child subtrees. The result concerns arbitrary leaf unions in this specified common-tree model. A covering-system application still requires its arithmetic identification and a sufficient avoidance or charge bound.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ConditionalComparison/CommonTreeUnion.union_conditioning`
