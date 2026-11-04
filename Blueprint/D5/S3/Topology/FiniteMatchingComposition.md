# First-return matching composition

## Abstract

The actual finite first-return pairing is exactly the outer partner relation of a glued matching network.

For finite X and involutive permutations s,r, let E=Fix(r) and P=endpointPairing(s,r). P uses the least positive return to E under s*r. The first-return construction and its involutivity come from FiniteEndpointPairing. InvolutionOrbitSplit supplies alternating connectivity as the union of two product orbits. Component(r) means the quotient by EqvGen(r); q(r,x) denotes the quotient class. Type parameters may occupy independent universes.

**Theorem 1.1 (Completeness of the actual endpoint pairing).**

$$\forall X \in FiniteType,\; \forall s \in \operatorname{Perm}\left(X\right),\; \forall r \in \operatorname{Perm}\left(X\right),\; \left(\operatorname{Involutive}\left(s\right) \land \operatorname{Involutive}\left(r\right)\right) \Rightarrow \left(\forall x \in \operatorname{Fix}\left(r\right),\; \forall y \in \operatorname{Fix}\left(r\right),\; \operatorname{q}\left(\operatorname{twoStep}\left(s, r\right), \operatorname{val}\left(x\right)\right) = \operatorname{q}\left(\operatorname{twoStep}\left(s, r\right), \operatorname{val}\left(y\right)\right) \Leftrightarrow \left(y = x \lor y = \operatorname{P}\left(s, r, x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingComposition.endpoint_component_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an r-fixed endpoint, s(x)=(s*r)(x), so the two candidate product orbits coincide. Reattachment with the identity identifies that orbit with the orbit of the actual first-return involution. Such an involution has only x and P(x) in the orbit. The theorem allows fixed points of s; freeness is required later to obtain distinct partners.

For N natural, Boundary(N)=Bool times Fin N. Piece(N) is one tagged copy of each input boundary. PiecesMate applies d on the first copy and e on the second. SeamMate exchanges the bottom of d with the top of e and fixes the exposed top and bottom. ExposedEquiv identifies those fixed points with Boundary(N). Composite(d,e) transports the actual endpoint pairing through this equivalence. Since both input matchings are free, Composite is a free involution as well. N=0 and N=1 are included.

**Theorem 1.2 (The first-return output is the genuine glued partner).**

$$\forall N \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right),\; \forall e \in \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right),\; \forall a \in \operatorname{Boundary}\left(N\right),\; \forall b \in \operatorname{Boundary}\left(N\right),\; \operatorname{q}\left(\operatorname{gluingStep}\left(d, e\right), \operatorname{outer}\left(a\right)\right) = \operatorname{q}\left(\operatorname{gluingStep}\left(d, e\right), \operatorname{outer}\left(b\right)\right) \Leftrightarrow \left(b = a \lor b = \operatorname{mate}\left(\operatorname{composite}\left(d, e\right), a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingComposition.triple_component_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit map collapse suppresses the seam wires onto the three-level graph. Retain chooses the upper copy of each seam vertex. Matching edges map to actual gluing edges; the only nontrivial fiber path is a seam edge. These maps induce halfToTripleEquiv and carry the actual exposed vertices to outer(a). Transporting the endpoint characterization proves the displayed equivalence.

**Theorem 1.3 (The same contraction preserves internal loops).**

$$\forall N \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right),\; \forall e \in \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right),\; \operatorname{internalLoopCount}\left(d, e\right) = \operatorname{card}\left(\operatorname{InternalComponent}\left(d, e\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingComposition.internalLoopCount_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

InternalLoopCount counts half-edge components with no exposed endpoint. HalfToTripleEquiv preserves each boundary class, hence restricts to an equivalence with InternalComponent in the literal three-level graph. This transports the actual component subtype, rather than postulating a circle-count identity.

The construction is classical finite matching calculus, with the existing first-return and orbit theorems reused directly. Four-layer associativity and the corresponding internal-loop inventory require further component-separation proofs. They are not assertions of this module.

## References

- Truth anchor: `D5/S3/Topology/FiniteMatchingComposition.endpoint_component_iff`
- Truth anchor: `D5/S3/Topology/FiniteMatchingComposition.internalLoopCount_eq`
- Truth anchor: `D5/S3/Topology/FiniteMatchingComposition.triple_component_iff`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing](../Combinatorics/PerfectMatchings/FiniteEndpointPairing.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit](../Combinatorics/PerfectMatchings/InvolutionOrbitSplit.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](FiniteMatchingClosure.md)
