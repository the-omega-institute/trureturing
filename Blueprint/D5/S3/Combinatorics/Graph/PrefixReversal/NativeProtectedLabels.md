# Fixed Protected Labels in Actual Recursive Frames

## Abstract

The final two selected labels form one fixed actual protected pair throughout native recursive frame growth and child-base rotation.

**Definition 1.1 (The Penultimate Selected Label).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \mathrm{ProtectedP}\left(frame\right) = \mathrm{ListGet}\left(\mathrm{Selected}\left(frame\right), \mathrm{NatSub}\left(k, 2\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.protectedP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every complete SupplyFrame(m,k) with k at least two, protectedP is the actual selected label at index k minus two. The supplied length proof earns that this index exists.

**Definition 1.2 (The Final Selected Label).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \mathrm{ProtectedQ}\left(frame\right) = \mathrm{ListGet}\left(\mathrm{Selected}\left(frame\right), \mathrm{NatSub}\left(k, 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.protectedQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual selected label at index k minus one is protectedQ. These labels are fixed by their list positions, without choosing another cycle or a separate relabelling.

**Theorem 1.3 (The Protected Pair Is Distinct and Outside the Base).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \left(\mathrm{Not}\left(\mathrm{ProtectedP}\left(frame\right) = \mathrm{ProtectedQ}\left(frame\right)\right) \land \left(\mathrm{Member}\left(\mathrm{ProtectedP}\left(frame\right), \mathrm{Selected}\left(frame\right)\right) \land \left(\mathrm{Member}\left(\mathrm{ProtectedQ}\left(frame\right), \mathrm{Selected}\left(frame\right)\right) \land \left(\mathrm{Not}\left(\mathrm{Member}\left(\mathrm{ProtectedP}\left(frame\right), \mathrm{Base}\left(frame\right)\right)\right) \land \left(\mathrm{Not}\left(\mathrm{Member}\left(\mathrm{ProtectedQ}\left(frame\right), \mathrm{Base}\left(frame\right)\right)\right) \land \left(\mathrm{Not}\left(\mathrm{ProtectedP}\left(frame\right) = \mathrm{Terminal}\left(frame\right)\right) \land \mathrm{Not}\left(\mathrm{ProtectedQ}\left(frame\right) = \mathrm{Terminal}\left(frame\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.native_protected_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full tuple nodup proves that the last two selected positions have different actual labels. The same tuple separates selected labels from the independent base and terminal. This supplies one nondegenerate pair for the a-edge retention invariant in the same actual recursive cycle.

**Theorem 1.4 (Prepending Preserves Both Labels).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \left(\forall next \in \mathrm{SupplyFrame}\left(m, \mathrm{NatAdd}\left(k, 1\right)\right),\; \forall u \in \mathrm{Fin}\left(\mathrm{NatAdd}\left(m, 1\right)\right),\; \mathrm{Selected}\left(next\right) = \mathrm{Cons}\left(u, \mathrm{Selected}\left(frame\right)\right) \Rightarrow \left(\mathrm{ProtectedP}\left(next\right) = \mathrm{ProtectedP}\left(frame\right) \land \mathrm{ProtectedQ}\left(next\right) = \mathrm{ProtectedQ}\left(frame\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.native_protected_labels_prepend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any actual next frame whose selected list is u cons the old selected list, both protected labels remain literally equal. The proof earns the shifted indices from k at least two. In particular, the native nextFrame constructor passes its defining selected-list equality.

**Theorem 1.5 (Child-Base Rotation Preserves Both Labels).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \left(\forall next \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{Selected}\left(next\right) = \mathrm{Selected}\left(frame\right) \Rightarrow \left(\mathrm{ProtectedP}\left(next\right) = \mathrm{ProtectedP}\left(frame\right) \land \mathrm{ProtectedQ}\left(next\right) = \mathrm{ProtectedQ}\left(frame\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.native_protected_labels_same_selected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any two complete frames with exactly the same selected list have the same protected labels. The nativeChildFrame operation rotates only the independent base, so it passes this premise by definition. This keeps the same pair across all ordinary children, without assuming that independently chosen cycle witnesses agree.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.native_protected_labels`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.native_protected_labels_prepend`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.native_protected_labels_same_selected`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.protectedP`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.protectedQ`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveSupply](NativeRecursiveSupply.md)
