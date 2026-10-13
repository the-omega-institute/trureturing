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

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.circle_neighbours`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_circle_gap_disjoint`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement](NativeCircleComplement.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches](NativeSwitches.md)
