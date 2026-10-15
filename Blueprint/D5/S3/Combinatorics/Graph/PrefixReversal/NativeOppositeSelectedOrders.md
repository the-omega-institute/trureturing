# Canonical Opposite Selected Orders

## Abstract

The two recursive marked orders are tied by one canonical exchange of the last two selected labels. Their earlier selected positions, base, terminal and child-base rotation retain exact literal identities.

**Definition 1.1 (Exchange Only the Protected Pair).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \mathrm{Selected}\left(\mathrm{OppositeSelectedFrame}\left(frame\right)\right) = \mathrm{Map}\left(\mathrm{Swap}\left(\mathrm{ProtectedP}\left(frame\right), \mathrm{ProtectedQ}\left(frame\right)\right), \mathrm{Selected}\left(frame\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.oppositeSelectedFrame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete SupplyFrame is rebuilt with the selected list mapped through the transposition of protectedP and protectedQ. Both labels occur in the original selected list, so the map is a permutation of that list. The independent base and terminal are literally unchanged. This fixes an ordering, rather than merely requiring equality of selected-label sets.

**Theorem 1.2 (The Protected Labels Exchange Positions).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \left(\mathrm{ProtectedP}\left(\mathrm{OppositeSelectedFrame}\left(frame\right)\right) = \mathrm{ProtectedQ}\left(frame\right) \land \mathrm{ProtectedQ}\left(\mathrm{OppositeSelectedFrame}\left(frame\right)\right) = \mathrm{ProtectedP}\left(frame\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_protected_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual labels at indices k minus two and k minus one exchange. No independently chosen opposite frame, cycle or relabelling is assumed.

**Theorem 1.3 (The Earlier Selected Prefix Is Unchanged).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \mathrm{Take}\left(\mathrm{NatSub}\left(k, 2\right), \mathrm{Selected}\left(\mathrm{OppositeSelectedFrame}\left(frame\right)\right)\right) = \mathrm{Take}\left(\mathrm{NatSub}\left(k, 2\right), \mathrm{Selected}\left(frame\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_selected_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nodup of the complete literal tuple separates each earlier selected position from both protected labels. The transposition therefore fixes every one of those positions. Along with the exchanged final pair, this determines the exact opposite selected order.

**Theorem 1.4 (The Canonical Exchange Is an Involution).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \mathrm{OppositeSelectedFrame}\left(\mathrm{OppositeSelectedFrame}\left(frame\right)\right) = frame$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_selected_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After one exchange the protected labels themselves are reversed. The second exchange uses the same unordered transposition, restoring the entire complete frame, including its unchanged base and terminal.

**Theorem 1.5 (The Exceptional J2 Order Uses the Same Exchange).**

$$\forall m \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; \mathrm{OppositeSelectedFrame}\left(frame\right) = \mathrm{ReverseSelected}\left(frame\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_selected_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At order two the protected pair is the entire selected list. The canonical exchange is exactly the existing reverseSelected frame used by the actual J2 seed, with the same base, terminal and port indices. This bridges the exceptional seed to the precise ordering required by later simultaneous states.

**Theorem 1.6 (Prepending Commutes with the Exchange).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \left(\forall A \in \mathrm{List}\left(\mathrm{Fin}\left(\mathrm{NatAdd}\left(m, 1\right)\right)\right),\; \forall u \in \mathrm{Fin}\left(\mathrm{NatAdd}\left(m, 1\right)\right),\; \mathrm{Base}\left(frame\right) = \mathrm{Append}\left(A, \mathrm{Singleton}\left(u\right)\right) \Rightarrow \mathrm{OppositeSelectedFrame}\left(\mathrm{NextFrame}\left(frame, A, u\right)\right) = \mathrm{NextFrame}\left(\mathrm{OppositeSelectedFrame}\left(frame\right), A, u\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_next_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an original base A append singleton u, nextFrame prepends u to the selected list. Full tuple nodup proves u differs from both protected labels; the protected-label prepend theorem keeps their literal identities. Hence constructing the next frame and taking its opposite commutes exactly. This gives compatible simultaneous induction instances rather than assuming agreement of separately chosen orders.

**Theorem 1.7 (The Outer Supplier Commutes with the Exchange).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \left(\forall A \in \mathrm{List}\left(\mathrm{Fin}\left(\mathrm{NatAdd}\left(m, 1\right)\right)\right),\; \forall u \in \mathrm{Fin}\left(\mathrm{NatAdd}\left(m, 1\right)\right),\; \mathrm{Base}\left(frame\right) = \mathrm{Append}\left(A, \mathrm{Singleton}\left(u\right)\right) \Rightarrow \mathrm{OppositeSelectedFrame}\left(\mathrm{OuterFrame}\left(frame, A, u\right)\right) = \mathrm{OuterFrame}\left(\mathrm{OppositeSelectedFrame}\left(frame\right), A, u\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_outer_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual outer supplier replaces the base by A append the old terminal and replaces the terminal by u. Its selected list keeps the old order. The canonical opposite operation therefore commutes with this same literal supplier constructor.

**Theorem 1.8 (Every Child-Base Rotation Commutes with the Exchange).**

$$\forall m \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall frame \in \mathrm{SupplyFrame}\left(m, k\right),\; \mathrm{AtLeast}\left(k, 2\right) \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right)\right),\; \mathrm{OppositeSelectedFrame}\left(\mathrm{NativeChildFrame}\left(frame, j\right)\right) = \mathrm{NativeChildFrame}\left(\mathrm{OppositeSelectedFrame}\left(frame\right), j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_child_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each independent child index, nativeChildFrame rotates the base by exactly that index and retains the selected list and terminal. Both marked orders therefore use the same literal child-base rotation. These order identities supply missing frame compatibility; they do not assert a completed all-order Hamiltonian induction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_child_frame`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_next_frame`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_outer_frame`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_protected_labels`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_selected_involutive`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_selected_prefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.native_opposite_selected_two`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.oppositeSelectedFrame`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameTransport](NativeJ2FrameTransport.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedFrameDomains](NativeMarkedFrameDomains.md)
