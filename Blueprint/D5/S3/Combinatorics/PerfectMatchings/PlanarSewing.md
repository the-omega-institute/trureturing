# Planar path sewing

## Abstract

Planar path sewing

NCMatching is a fixed-point-free involutive permutation without interleaving chords. The circular rectangle order goes left to right along the top and right to left along the bottom. Adjacent seam elimination preserves noncrossing and gives the path-defined rectangle composite.

**Definition 1.1 (capStep).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}\left((m) + (2)\right)), (\forall (j: \operatorname{Fin}\left((m) + (1)\right)), (\forall (x: \operatorname{Fin}\left((m) + (2)\right)), (\forall (y: \operatorname{Fin}\left((m) + (2)\right)), (\operatorname{capStep}\left(M, j, x, y\right) = \left((y = \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}.\operatorname{partner}\left(M, x\right)) \lor ((x = \operatorname{Fin}.\operatorname{castSucc}\left(j\right)) \land (y = \operatorname{Fin}.\operatorname{succ}\left(j\right)))\right))))))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The relation is an original matching edge or the oriented adjacent seam.

**Theorem 1.2 (capSurgery_component_iff).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}\left((m) + (2)\right)), (\forall (j: \operatorname{Fin}\left((m) + (1)\right)), (\forall (x: \operatorname{Fin}\left(m\right)), (\forall (y: \operatorname{Fin}\left(m\right)), ((\operatorname{Relation}.\operatorname{EqvGen}\left(\operatorname{capStep}\left(M, j\right), \operatorname{skipPair}\left(j, x\right), \operatorname{skipPair}\left(j, y\right)\right)) \Leftrightarrow ((y = x) \lor (y = \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}.\operatorname{partner}\left(\operatorname{capSurgery}\left(M, j\right), x\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capSurgery_component_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The surviving relation is precisely equality or the mate relation after cap surgery.

**Definition 1.3 (boundaryEquiv).**

$$\forall (n: \operatorname{Nat}), (\operatorname{boundaryEquiv}\left(n\right) = \operatorname{Equiv}.\operatorname{trans}\left(\operatorname{Equiv}.\operatorname{boolProdEquivSum}\left(\operatorname{Fin}\left(n\right)\right), \operatorname{Equiv}.\operatorname{trans}\left(\operatorname{Equiv}.\operatorname{sumCongr}\left(\operatorname{Equiv}.\operatorname{refl}\left(\operatorname{Fin}\left(n\right)\right), (\operatorname{Fin}.\operatorname{revPerm}: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right))\right), \operatorname{Equiv}.\operatorname{trans}\left(\operatorname{finSumFinEquiv}, \operatorname{finCongr}\left(\operatorname{by} \operatorname{omega}\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.boundaryEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The last congruence identifies n+n with 2*n. Equiv.toFun sends a top port to i and a bottom port to n+(n-1-i).

**Definition 1.4 (toMatching).**

$$\forall (n: \operatorname{Nat}), (\forall (M: \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}\left((2) \cdot (n)\right)), (\operatorname{Matching}.\operatorname{mate}\left(\operatorname{toMatching}\left(M\right)\right) = ((x: \operatorname{Boundary}\left(n\right)) \mapsto \operatorname{Equiv}.\operatorname{toFun}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{boundaryEquiv}\left(n\right)\right), \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}.\operatorname{partner}\left(M, \operatorname{Equiv}.\operatorname{toFun}\left(\operatorname{boundaryEquiv}\left(n\right), x\right)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.toMatching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the literal mate field. Its involution and fixed-point-free proof fields follow from M.involutive and M.noFixed under the displayed equivalence. Matching records with equal mate fields are equal.

**Theorem 1.5 (composite_planar).**

$$\forall (n: \operatorname{Nat}), (\forall (M: \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}\left((2) \cdot (n)\right)), (\forall (N: \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}\left((2) \cdot (n)\right)), (\exists (Q: \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}\left((2) \cdot (n)\right)), (\operatorname{toMatching}\left(Q\right) = \operatorname{composite}\left(\operatorname{toMatching}\left(M\right), \operatorname{toMatching}\left(N\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.composite_planar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Path composition of two planar matchings is planar, including products with internal loops.

**Theorem 1.6 (identity_planar).**

$$\forall (n: \operatorname{Nat}), (\exists (Q: \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}\left((2) \cdot (n)\right)), (\operatorname{toMatching}\left(Q\right) = \operatorname{identityMatching}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.identity_planar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reversal of the circular boundary gives the rectangle identity.

**Definition 1.7 (capReconnection).**

$$\forall (m: \operatorname{Nat}), (\forall (M: \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}\left((m) + (2)\right)), (\forall (j: \operatorname{Fin}\left((m) + (1)\right)), (\operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}.\operatorname{partner}\left(\operatorname{capReconnection}\left(M, j\right)\right) = \operatorname{capConjugate}\left(M, j\right))))$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.capReconnection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the literal partner field. The involutive and noFixed fields are capConjugate_involutive M j and capConjugate_noFixed M j. Adjacent reconnection supplies noncrossing; the proof fields do not change the partner permutation.

**Theorem 1.8 (cupcap_planar).**

$$\forall (n: \operatorname{Nat}), (\forall (j: \operatorname{Nat}), (\forall (hj: (j) + (1) < n), (\exists (Q: \operatorname{CupCapBridgeProposal}.\operatorname{NCMatching}\left((2) \cdot (n)\right)), (\operatorname{toMatching}\left(Q\right) = \operatorname{cupcapMatching}\left(j, hj\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/PlanarSewing.cupcap_planar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard adjacent cup-cap has a noncrossing representative.

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
