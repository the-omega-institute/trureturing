# Physical histories and target inventory

## Abstract

A complete physical forest supplies the canonical target inventory and original same-digit assignments.

PhysicalForest retains every original label and indexed read event, its unique forest parent, absolute digit, cumulative literal wait, original leaf output and exact phase interval. The three roots use the digit of x+ell; each path has a positive finite read count at most h. All child waits are positive literal integers. Singleton continuations are retained. History levels order the forest; they impose no order on read-control states.

Prescribed retains the marked physical source nodes A,B,H,K,H1,K1, their roles, disjoint physical supports, equal literal requests and original child digits. A represents the merged A/B binary target. Z and Fin e extras are separate tags. H may equal A or B, so its target may be Q. Z remains outside all binary targets.

Compatible checks only the forced source rows: equal rows may contain the same node, H/K, or H1/K1. It mentions no controller, execution, alpha, resource injection or capacity. The operational owner derives this check from OriginalImplementation and proves the incompatible branch empty.

Ordinary demands are exactly unary nodes excluding K,H1,K1. Assignment injects them into unoccupied absolute-digit slots, preserves each child's digit and hits every extra target. A baseline is the maximum binary-parent literal request, the resolving request at Z, or one for an extra. L is the joint maximum of that baseline and every assigned demand. All three spare digits of one extra therefore share one maximum.

**Theorem 1.1 (Exactly the original fixed-label leaves).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\operatorname {card}(\operatorname {completeLeaves}(F))=3P}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory.leaf_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an original label in a leaf support. Its event must be final, since a further event would supply a child. Conversely every label's last event is a leaf and has that fixed output. This gives a leaf-label equivalence and exactly 3P leaves. The root colors give exactly three distinct roots. Singleton continuation nodes remain internal.

**Theorem 1.2 (No additional history collision).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall e:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{{\operatorname {Compatible}(F,R,e)}\implies{\forall n:Node,{\forall m:Node,{{\operatorname {placement}(F,R,alpha,n)=\operatorname {placement}(F,R,alpha,m)}\implies{\operatorname {Shared}(F,R,n,m)}}}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory.placement_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forced rows use source incidence; ordinary rows use same-digit spare slots. A spare row cannot meet a forced row, and injectivity prevents ordinary demands from sharing a row.

**Theorem 1.3 (Every literal source request fits its joint target tail).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall e:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{\forall alpha:\operatorname {Assignment}(F,R,e),{\forall n:Node,{{\operatorname {Internal}(F,n)}\implies{\operatorname {delay}(F,n)\le\operatorname {L}(F,R,alpha,\operatorname {nextTarget}(F,R,alpha,n))}}}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory.request_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Binary requests are included in the baseline. K shares H's literal request. H1/K1 share the resolving request. Every remaining unary request is included through alpha.

**Theorem 1.4 (The canonical 3/2/2/0 inventory).**

$$\forall P:\mathbb {N},{\forall h:\mathbb {N},{\forall ell:\mathbb {N},{\forall e:\mathbb {N},{\forall Node:Type,{[\operatorname {Fintype}(Node)][\operatorname {DecidableEq}(Node)]\forall hP:1<P,{\forall F:\operatorname {PhysicalForest}(P,h,ell,Node,hP),{\forall R:\operatorname {Prescribed}(F),{\forall q:\operatorname {Target}(F,R,e),{\operatorname {card}(\operatorname {occupied}(F,R,q))=\operatorname {occupiedDigitCount}(R,q)}}}}}}}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory.occupied_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The A/B representative Q occupies three digits, every other binary target two, Z two and every extra zero before assignment. The count follows from the original parent and child-digit incidence, including the absorbed K arrival.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory.leaf_count`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory.occupied_counts`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory.placement_fibers`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory.request_bound`
- Dependency: [D5/S3/ObserverMemory/Algorithms/StationaryUnitControl](StationaryUnitControl.md)
