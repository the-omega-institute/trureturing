# Native Circle Ownership

## Abstract

Actual native circle domains from distinct insertion gaps are disjoint.

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

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.circle_neighbours`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_circle_gap_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_cross_circle_disjoint`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement](NativeCircleComplement.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches](NativeSwitches.md)
