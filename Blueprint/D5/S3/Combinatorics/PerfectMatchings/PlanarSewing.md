# Planar path sewing

## Abstract

Planar path sewing

NCMatching is a fixed-point-free involutive permutation of a finite cyclic boundary without interleaving chords. BoundaryEquiv lists the top ports from left to right and then the bottom ports from right to left. Finite tagged matching networks are contracted by explicit maps. The adjacent seam relation is equality or one original matching edge or the new seam, closed under equivalence. Repeated adjacent seam elimination gives exactly the path-defined rectangle composite.

**Definition 1.1 (capStep).**

$$\forall m \in Nat,\; \forall M \in \operatorname{NCMatching}\left(\operatorname{Add}\left(m, 2\right)\right),\; \forall j \in \operatorname{Fin}\left(\operatorname{Add}\left(m, 1\right)\right),\; \forall x \in \operatorname{Fin}\left(\operatorname{Add}\left(m, 2\right)\right),\; \forall y \in \operatorname{Fin}\left(\operatorname{Add}\left(m, 2\right)\right),\; \operatorname{capStep}\left(M, j, x, y\right) \Leftrightarrow \left(y = \operatorname{partner}\left(M, x\right) \lor \left(x = \operatorname{castSucc}\left(j\right) \land y = \operatorname{succ}\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The relation contains each original matching edge and one adjacent seam.

**Theorem 1.2 (capSurgery_component_iff).**

$$\forall m \in Nat,\; \forall M \in \operatorname{NCMatching}\left(\operatorname{Add}\left(m, 2\right)\right),\; \forall j \in \operatorname{Fin}\left(\operatorname{Add}\left(m, 1\right)\right),\; \forall x \in \operatorname{Fin}\left(m\right),\; \forall y \in \operatorname{Fin}\left(m\right),\; \operatorname{EqvGen}\left(\operatorname{capStep}\left(M, j\right), \operatorname{skipPair}\left(j, x\right), \operatorname{skipPair}\left(j, y\right)\right) \Leftrightarrow \left(y = x \lor y = \operatorname{partner}\left(\operatorname{capSurgery}\left(M, j\right), x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capSurgery_component_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The survivor relation records precisely the reconnection after consuming adjacent ports, including an already paired input.

**Definition 1.3 (boundaryEquiv).**

$$\forall n \in Nat,\; \operatorname{boundaryEquiv}\left(n\right) = \operatorname{ComposeEquiv}\left(\operatorname{boolProdEquivSum}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{ComposeEquiv}\left(\operatorname{sumCongr}\left(Identity, Reverse\right), finSumFinEquiv\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.boundaryEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The final Fin congruence identifies n+n with 2*n. Top(b,i) has value i; bottom(b,i) has value n+(n-1-i).

**Definition 1.4 (toMatching).**

$$\forall n \in Nat,\; \forall M \in \operatorname{NCMatching}\left(\operatorname{Twice}\left(n\right)\right),\; \operatorname{toMatching}\left(M\right) = \operatorname{MatchingFromInvolution}\left(\operatorname{Conjugate}\left(\operatorname{Inverse}\left(\operatorname{boundaryEquiv}\left(n\right)\right), \operatorname{partner}\left(M\right), \operatorname{boundaryEquiv}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.toMatching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conjugation is on the actual endpoints; it forgets only the noncrossing proof.

**Theorem 1.5 (composite_planar).**

$$\forall n \in Nat,\; \forall M \in \operatorname{NCMatching}\left(\operatorname{Twice}\left(n\right)\right),\; \forall P \in \operatorname{NCMatching}\left(\operatorname{Twice}\left(n\right)\right),\; \exists Q \in \operatorname{NCMatching}\left(\operatorname{Twice}\left(n\right)\right),\; \operatorname{toMatching}\left(Q\right) = \operatorname{composite}\left(\operatorname{toMatching}\left(M\right), \operatorname{toMatching}\left(P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.composite_planar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The contraction identifies both endpoint components with the actual composite. Noncrossing closure holds for all products, with any number of internal loops.

**Theorem 1.6 (identity_planar).**

$$\forall n \in Nat,\; \exists Q \in \operatorname{NCMatching}\left(\operatorname{Twice}\left(n\right)\right),\; \operatorname{toMatching}\left(Q\right) = \operatorname{identityMatching}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.identity_planar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reverse pairing on the cyclic boundary is the rectangle identity.

**Definition 1.7 (capReconnection).**

$$\forall m \in Nat,\; \forall M \in \operatorname{NCMatching}\left(\operatorname{Add}\left(m, 2\right)\right),\; \forall j \in \operatorname{Fin}\left(\operatorname{Add}\left(m, 1\right)\right),\; \operatorname{capReconnection}\left(M, j\right) = \operatorname{NCMatchingFromPartner}\left(\operatorname{capConjugate}\left(M, j\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capReconnection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CapConjugate is the conjugation swap(succ(j),partner(castSucc(j))) composed with partner and the same swap. Its partner is an involution without fixed points, and the adjacent reconnection preserves noncrossing.

**Theorem 1.8 (cupcap_planar).**

$$\forall n \in Nat,\; \forall j \in Nat,\; \operatorname{Less}\left(\operatorname{Add}\left(j, 1\right), n\right) \Rightarrow \left(\exists Q \in \operatorname{NCMatching}\left(\operatorname{Twice}\left(n\right)\right),\; \operatorname{toMatching}\left(Q\right) = \operatorname{cupcapMatching}\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.cupcap_planar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cup-cap matching pairs j,j+1 on each side and sends every other port straight through. It is the adjacent reconnection of the identity.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.boundaryEquiv`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capReconnection`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capStep`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capSurgery_component_iff`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.composite_planar`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.cupcap_planar`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.identity_planar`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.toMatching`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery](AdjacentCapSurgery.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerSourceMonoids](AraujoBrauerSourceMonoids.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore](OrderedMatchingCore.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](../../Topology/FiniteMatchingClosure.md)
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](../../Topology/FiniteMatchingComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingSewing](../../Topology/FiniteMatchingSewing.md)
