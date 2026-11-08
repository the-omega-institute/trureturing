# Associative matching sewing

## Abstract

Associative matching sewing

Boundary(n) is Bool times Fin(n). Composite follows paths in the glued middle boundary. InternalLoopCount counts connected components avoiding every exposed endpoint. No planarity assumption is used. A closed triple network is partitioned into the components removed in the first sewing and those removed in the second sewing; rotating its three matching layers preserves the closed inventory.

**Theorem 1.1 (composite_assoc).**

$$\forall n \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \forall e \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \forall f \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \operatorname{composite}\left(\operatorname{composite}\left(d, e\right), f\right) = \operatorname{composite}\left(d, \operatorname{composite}\left(e, f\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingAssociativity.composite_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both bracketings induce the same equivalence relation on the exterior boundary through partitionProduct associativity.

**Theorem 1.2 (internalLoopCount_cocycle).**

$$\forall n \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \forall e \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \forall f \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \operatorname{Add}\left(\operatorname{internalLoopCount}\left(d, e\right), \operatorname{internalLoopCount}\left(\operatorname{composite}\left(d, e\right), f\right)\right) = \operatorname{Add}\left(\operatorname{internalLoopCount}\left(e, f\right), \operatorname{internalLoopCount}\left(d, \operatorname{composite}\left(e, f\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingAssociativity.internalLoopCount_cocycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two sums count the same closed components of the triple gluing. The disjoint component equivalences retain internal components from both stages.

**Theorem 1.3 (internalLoopCount_pos_assoc).**

$$\forall n \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \forall e \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \forall f \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \left(\operatorname{Positive}\left(\operatorname{internalLoopCount}\left(d, e\right)\right) \lor \operatorname{Positive}\left(\operatorname{internalLoopCount}\left(\operatorname{composite}\left(d, e\right), f\right)\right)\right) \Leftrightarrow \left(\operatorname{Positive}\left(\operatorname{internalLoopCount}\left(e, f\right)\right) \lor \operatorname{Positive}\left(\operatorname{internalLoopCount}\left(d, \operatorname{composite}\left(e, f\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingAssociativity.internalLoopCount_pos_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer component identity implies equivalence of the two loop flags.

## References

- Truth anchor: `D5/S3/Topology/FiniteMatchingAssociativity.composite_assoc`
- Truth anchor: `D5/S3/Topology/FiniteMatchingAssociativity.internalLoopCount_cocycle`
- Truth anchor: `D5/S3/Topology/FiniteMatchingAssociativity.internalLoopCount_pos_assoc`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids](../Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](FiniteMatchingClosure.md)
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](FiniteMatchingComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingSewing](FiniteMatchingSewing.md)
