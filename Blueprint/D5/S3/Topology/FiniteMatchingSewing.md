# Sewing inventories and cyclic closure

## Abstract

Actual component labels partition sewn matching networks into untouched components and the sewn boundary quotient.

Let r be any edge relation on X, a:B to X a boundary map, d a matching on B and t:B to B arbitrary. EndpointCharacterization(r,a,d) abbreviates the exact assertion: for all b,c in B, q(r,a(b))=q(r,a(c)) if and only if c=b or c=mate(d,b). No finiteness is required. SewStep(r,a,t) adds all edges from a(b) to a(t(b)). Unmarked(r,a) is the subtype of components of r containing no a(b). TwoStep(f,g) has edges y=f(x) or y=g(x). Component is the actual equivalence-closure quotient, and Equiv denotes a constructed bijection.

**Definition 1.1 (A component inventory constructed by labels).**

$$\forall X \in Type,\; \forall B \in Type,\; \forall r \in \operatorname{Relation}\left(X\right),\; \forall a \in \operatorname{Maps}\left(B, X\right),\; \forall d \in \operatorname{Matching}\left(B\right),\; \forall t \in \operatorname{Maps}\left(B, B\right),\; \operatorname{EndpointCharacterization}\left(r, a, d\right) \Rightarrow \operatorname{Equiv}\left(\operatorname{Component}\left(\operatorname{sewStep}\left(r, a, t\right)\right), \operatorname{Sum}\left(\operatorname{Unmarked}\left(r, a\right), \operatorname{Component}\left(\operatorname{twoStep}\left(\operatorname{mate}\left(d\right), t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Topology/FiniteMatchingSewing.sewingInventory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An old component with no boundary point retains its own label. For a component meeting the boundary, choose one boundary representative and use its class in the twoStep quotient. The partner characterization makes the choice independent of the representative. Added sewing edges preserve that label. Conversely, untouched components embed into the sewn network and boundary classes map through a. These maps are inverse on the actual quotients.

For the following formulas N is any natural number, Boundary(N)=Bool times Fin N and d,e are arbitrary matchings of that boundary. InternalLoopCount counts internal components of the first-return gluing. ClosedComponent(d) is Component(twoStep(mate(d),mate(identityMatching(N)))); closedCount(d) is its Nat.card. ClosedStackStep(d,e) is the actual disjoint two-matching network with both seam and closure wires. Sum means disjoint union and add is natural-number addition.

**Definition 1.2 (Close before or after actual matching composition).**

$$\forall N \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right),\; \forall e \in \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right),\; \operatorname{Equiv}\left(\operatorname{Component}\left(\operatorname{closedStackStep}\left(d, e\right)\right), \operatorname{Sum}\left(\operatorname{halfEdgeInternalComponent}\left(d, e\right), \operatorname{ClosedComponent}\left(\operatorname{composite}\left(d, e\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Topology/FiniteMatchingSewing.closedStackInventory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Closing the exposed boundary is sewing with the identity matching. The actual first-return component theorem discharges EndpointCharacterization; it is not an extra hypothesis of this result. A direct equivalence identifies the sewn graph with the literal closed stack. Thus every closed component is either an internal gluing component or a component of the closed composite.

**Theorem 1.3 (Cyclic closure preserves the complete circle exponent).**

$$\forall N \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right),\; \forall e \in \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right),\; \operatorname{add}\left(\operatorname{internalLoopCount}\left(d, e\right), \operatorname{closedCount}\left(\operatorname{composite}\left(d, e\right)\right)\right) = \operatorname{add}\left(\operatorname{internalLoopCount}\left(e, d\right), \operatorname{closedCount}\left(\operatorname{composite}\left(e, d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingSewing.closed_weight_cyclic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weight(d,e) abbreviates internalLoopCount(d,e)+closedCount(composite(d,e)). The inventory identifies this sum with the number of components of the actual closed stack. Exchanging the two tagged layers preserves every matching edge and closure wire. The resulting quotient equivalence proves Weight(d,e)=Weight(e,d). This is a count identity for all pairings; no planarity, coefficient ring, invertible circle value or supplied trace identity is involved.

**Theorem 1.4 (The identity has exactly N closure circles).**

$$\forall N \in Nat,\; \operatorname{closedCount}\left(\operatorname{identityMatching}\left(N\right)\right) = N$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingSewing.closedCount_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index projection identifies each closed identity component with its Fin N label. In particular N=0 contributes zero circles, without an extra empty-diagram circle. Every matching on Boundary(0) equals identityMatching(0) by extensionality on the empty boundary, so the same count applies to every empty matching.

Straight matchings are also proved to be left and right units for the actual composite, with zero internal loops. The unit contractions retain every outer boundary vertex. This is the classical Brauer pairing and circle-removal construction. Associative multiplication on the free module, the tower inclusion, the local Temperley--Lieb relations and Jones identification are separate assertions.

## References

- Truth anchor: `D5/S3/Topology/FiniteMatchingSewing.closedCount_identity`
- Truth anchor: `D5/S3/Topology/FiniteMatchingSewing.closedStackInventory`
- Truth anchor: `D5/S3/Topology/FiniteMatchingSewing.closed_weight_cyclic`
- Truth anchor: `D5/S3/Topology/FiniteMatchingSewing.sewingInventory`
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](FiniteMatchingComposition.md)
