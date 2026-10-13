# Native Circle Ownership

## Abstract

The actual two T supplier stars intersect in exactly two core circles and their union has a unique complete circle owner.

The ownership argument compares actual tuple cycles. Rotation preserves both cyclic neighbours of every label and whole reversal exchanges next with previous. Existing coordinate equivalence then proves that two distinct insertion gaps cannot share a complete circle.

**Theorem 1.1 (Distinct Insertion Gaps Have Disjoint Circle Domains).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \forall i \in \mathrm{Fin}\left(m\right),\; \forall j \in \mathrm{Fin}\left(m\right),\; \left(\neg i = j\right) \Rightarrow \mathrm{Disjoint}\left(\mathrm{circleDomain}\left(\mathrm{gapAnchor}\left(z, i\right)\right), \mathrm{circleDomain}\left(\mathrm{gapAnchor}\left(z, j\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_circle_gap_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is an actual support statement for the F2 supplier decomposition. It uses the literal rotation/reversal quotient and does not infer ownership from a chosen path.

**Theorem 1.2 (Circle Ownership Preserves the Unordered Cyclic Neighbours).**

$$\forall m \in \mathrm{Nat},\; \forall z \in \mathrm{Configuration}\left(m\right),\; \forall v \in \mathrm{Configuration}\left(m\right),\; \forall x \in \mathrm{Fin}\left(\mathrm{add}\left(m, 1\right)\right),\; \mathrm{Circle}\left(z, v\right) \Rightarrow \left(\left(\mathrm{nextLabel}\left(v, x\right) = \mathrm{nextLabel}\left(z, x\right) \land \mathrm{prevLabel}\left(v, x\right) = \mathrm{prevLabel}\left(z, x\right)\right) \lor \left(\mathrm{nextLabel}\left(v, x\right) = \mathrm{prevLabel}\left(z, x\right) \land \mathrm{prevLabel}\left(v, x\right) = \mathrm{nextLabel}\left(z, x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.circle_neighbours` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual tuple rotations preserve next and previous labels, while whole reversal exchanges them. This invariant is the reusable boundary for cross-supplier ownership.

**Theorem 1.3 (The Two Native T Suppliers Have Disjoint Circle Domains).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall i \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{Disjoint}\left(\mathrm{circleDomain}\left(\mathrm{mul}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{pow}\left(\mathrm{mul}\left(\mathrm{b}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{val}\left(i\right)\right)\right)\right), \mathrm{circleDomain}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{pow}\left(\mathrm{mul}\left(\mathrm{b}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{val}\left(j\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_cross_circle_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least four, the lower ports a*c*(bc)^i and the upper ports swap(0,last)*a*c*(bc)^j have disjoint complete rotation-and-reversal circle domains. At the label m, the lower neighbours are 1 and m-1, whereas the upper neighbours are j+2 and either 1 or j+1; the unordered-neighbour invariant then gives the arithmetic contradiction.

**Theorem 1.4 (The Two Complete Supplier Stars Intersect Exactly in Their Core Circles).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{Star}\left(\mathrm{apply}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{last}\left(m\right)\right), \mathrm{residualList}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right), v\right) \land \mathrm{Star}\left(\mathrm{apply}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right), \mathrm{last}\left(m\right)\right), \mathrm{residualList}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right)\right), v\right)\right) \Leftrightarrow \left(\mathrm{Circle}\left(1, v\right) \lor \mathrm{Circle}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_core_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two stars are defined independently by actual deletion of the label in the last position of a*c or swap(0,last)*a*c. Their intersection consists precisely of the complete circles based at the identity and swap(0,last). The two final insertion gaps are computed pointwise; all other shared ownership is excluded by the actual cross-circle theorem. This supplies the two core domains required by the F2 splice, without assuming a path partition.

**Theorem 1.5 (The Full Two-Star Union Has Exactly One Complete Circle Owner).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{Star}\left(\mathrm{apply}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{last}\left(m\right)\right), \mathrm{residualList}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right), v\right) \lor \mathrm{Star}\left(\mathrm{apply}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right), \mathrm{last}\left(m\right)\right), \mathrm{residualList}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right)\right), v\right)\right) \Leftrightarrow \left(\exists p \in \mathrm{Sum}\left(\mathrm{Fin}\left(m\right), \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right)\right),\; \mathrm{Circle}\left(\mathrm{tCircleAnchor}\left(p\right), v\right) \land \left(\forall q \in \mathrm{Sum}\left(\mathrm{Fin}\left(m\right), \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right)\right),\; \mathrm{Circle}\left(\mathrm{tCircleAnchor}\left(q\right), v\right) \Rightarrow q = p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_circle_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cut-owner index is Fin(m) plus Fin(m-2). Its first family comprises all lower insertion gaps, including the two shared cores; its second family comprises just the upper noncore ports. Every actual vertex in the independently specified union belongs to exactly one complete indexed circle. Full gap exhaustion supplies existence, and the earned core classification and disjointness supply uniqueness. This is a support partition; actual F2 path splicing and the higher marked-path induction remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.circle_neighbours`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_circle_gap_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_circle_partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_core_intersection`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_cross_circle_disjoint`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement](NativeCircleComplement.md)
