# Characteristic-seven six-column detour

## Abstract

Six-column affine group action and the overlapping two-head characteristic-seven splice.

The generic row-return theorem supplies the affine orbit calculation. This document records the genuinely new six-phase lift in ZMod(7), its exact inventories, and the full relative path produced by the overlapping endpoint splice. These are formal proofs of the stated construction, with no claim of literature novelty.

**Theorem 1.1 (Exact six-phase cycles and inventories).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall f \in \operatorname{Field}\left(K\right),\; \forall finite \in \operatorname{Finite}\left(K\right),\; \forall char \in \operatorname{CharP}\left(K, 7\right),\; \forall c \in K,\; \exists r \in \operatorname{Units}\left(K\right),\; \operatorname{coe}\left(r\right) + 1 \ne 0 \land \left(\left(\forall v \in \operatorname{Fin}\left(6\right) \times K,\; \forall w \in \operatorname{Fin}\left(6\right) \times K,\; \operatorname{SameCycle}\left(\operatorname{lift}\left(r, c\right), v, w\right) \Leftrightarrow \left(\operatorname{initialRow}\left(v\right) = c \Leftrightarrow \operatorname{initialRow}\left(w\right) = c\right)\right) \land \left(\operatorname{BijOn}\left(\operatorname{edgeLabel}\left(r, c\right), \operatorname{univ}\left(\right), \{v:\operatorname{ZMod}\left(7\right) \times K\mid\operatorname{fst}\left(v\right) \ne 0\}\right) \land \left(\operatorname{BijOn}\left(\operatorname{vertex}\left(\right), \operatorname{univ}\left(\right), \{v:\operatorname{ZMod}\left(7\right) \times K\mid\operatorname{fst}\left(v\right) \ne 0\}\right) \land \left(\forall h \in K,\; \left(\operatorname{lift}\left(r, c\right)^{6}\right)\left((0,h)\right) = (0,\operatorname{rowReturn}\left(r, c\right)\left(h\right))\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/CharacteristicSevenDetour.exists_characteristic_seven_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A primitive unit gives the two affine row cycles. The six first-coordinate differences are the nonzero elements of F7, and each row-coordinate map is invertible. The vertex and label BijOn statements therefore cover every nonzero column exactly once over arbitrary finite extensions.

**Theorem 1.2 (Overlapping endpoint seams).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall f \in \operatorname{Field}\left(K\right),\; \forall char \in \operatorname{CharP}\left(K, 7\right),\; \forall r \in \operatorname{Units}\left(K\right),\; \forall u \in K,\; u \ne 0 \Rightarrow \left(\operatorname{coe}\left(r\right) + 1 \ne 0 \Rightarrow \left(\operatorname{splice}\left(r, u\right)\left(\operatorname{predecessorOne}\left(r, u\right)\right) = \operatorname{headTwo}\left(r, u\right) \land \left(\operatorname{splice}\left(r, u\right)\left(\operatorname{predecessorTwo}\left(r, u\right)\right) = \operatorname{target}\left(\right) \land \left(\operatorname{splice}\left(r, u\right)\left(\operatorname{source}\left(\right)\right) = \operatorname{headOne}\left(r, u\right) \land \left(\operatorname{splice}\left(r, u\right)\left(\operatorname{target}\left(\right)\right) = \operatorname{source}\left(\right) \land \left(\operatorname{vertexWithEndpoints}\left(u, \operatorname{headTwo}\left(r, u\right)\right) - \operatorname{vertexWithEndpoints}\left(u, \operatorname{predecessorOne}\left(r, u\right)\right) = (0,u) \land \left(\operatorname{vertexWithEndpoints}\left(u, \operatorname{target}\left(\right)\right) - \operatorname{vertexWithEndpoints}\left(u, \operatorname{predecessorTwo}\left(r, u\right)\right) = (2,2 \cdot \operatorname{alpha}\left(r, u\right)) \land \left(\operatorname{vertexWithEndpoints}\left(u, \operatorname{headOne}\left(r, u\right)\right) - \operatorname{vertexWithEndpoints}\left(u, \operatorname{source}\left(\right)\right) = (3,\operatorname{alpha}\left(r, u\right)) \land \operatorname{vertexWithEndpoints}\left(u, \operatorname{source}\left(\right)\right) - \operatorname{vertexWithEndpoints}\left(u, \operatorname{target}\left(\right)\right) = (0,-u)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/CharacteristicSevenDetour.six_column_splice_seams` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With alpha=(r+1)u/(3r), c=-alpha and beta=u-alpha, the two heads have initial rows c and c+u. The predecessor equations and all four actual seam labels are retained before the closing target-to-source edge is deleted.

**Theorem 1.3 (Complete relative path over every finite characteristic-seven field).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall f \in \operatorname{Field}\left(K\right),\; \forall finite \in \operatorname{Finite}\left(K\right),\; \forall char \in \operatorname{CharP}\left(K, 7\right),\; \forall u \in K,\; u \ne 0 \Rightarrow \left(\exists v \in \operatorname{Function}\left(\operatorname{Nat}\left(\right), \operatorname{ZMod}\left(7\right) \times K\right),\; \exists w \in \operatorname{Function}\left(\operatorname{Nat}\left(\right), \operatorname{ZMod}\left(7\right) \times K\right),\; v\left(0\right) = (0,0) \land \left(v\left(6 \cdot \operatorname{card}\left(K\right) + 1\right) = (0,u) \land \left(\operatorname{Injective}\left(\operatorname{restrict}\left(v, \operatorname{Fin}\left(6 \cdot \operatorname{card}\left(K\right) + 1 + 1\right)\right)\right) \land \left(\operatorname{range}\left(\operatorname{interior}\left(v, 6 \cdot \operatorname{card}\left(K\right) + 1 - 1\right)\right) = \{z:\operatorname{ZMod}\left(7\right) \times K\mid\operatorname{fst}\left(z\right) \ne 0\} \land \left(\left(\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{lt}\left(n, 6 \cdot \operatorname{card}\left(K\right) + 1\right) \Rightarrow w\left(n\right) = v\left(n + 1\right) - v\left(n\right)\right) \land \left(\operatorname{Injective}\left(\operatorname{restrict}\left(w, \operatorname{Fin}\left(6 \cdot \operatorname{card}\left(K\right) + 1\right)\right)\right) \land \left(\operatorname{range}\left(\operatorname{restrict}\left(w, \operatorname{Fin}\left(6 \cdot \operatorname{card}\left(K\right) + 1\right)\right)\right) = \{z:\operatorname{ZMod}\left(7\right) \times K\mid\operatorname{fst}\left(z\right) \ne 0\} \cup \{(0,u)\} \land \left(\operatorname{length}\left(\operatorname{ofFn}\left(\operatorname{restrict}\left(v, \operatorname{Fin}\left(6 \cdot \operatorname{card}\left(K\right) + 1 + 1\right)\right)\right)\right) = 6 \cdot \operatorname{card}\left(K\right) + 1 + 1 \land \left(\operatorname{length}\left(\operatorname{ofFn}\left(\operatorname{restrict}\left(w, \operatorname{Fin}\left(6 \cdot \operatorname{card}\left(K\right) + 1\right)\right)\right)\right) = 6 \cdot \operatorname{card}\left(K\right) + 1 \land \left(\operatorname{Nodup}\left(\operatorname{ofFn}\left(\operatorname{restrict}\left(v, \operatorname{Fin}\left(6 \cdot \operatorname{card}\left(K\right) + 1 + 1\right)\right)\right)\right) \land \left(\operatorname{Nodup}\left(\operatorname{ofFn}\left(\operatorname{restrict}\left(w, \operatorname{Fin}\left(6 \cdot \operatorname{card}\left(K\right) + 1\right)\right)\right)\right) \land \left(\left(\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{le}\left(n, 6 \cdot \operatorname{card}\left(K\right) + 1\right) \Rightarrow \operatorname{sum}\left(\operatorname{range}\left(n\right), w\right) = v\left(n\right)\right) \land \left(\operatorname{Injective}\left(\operatorname{boundedPrefixes}\left(w, 6 \cdot \operatorname{card}\left(K\right) + 1 + 1\right)\right) \land \left(\left(\forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; \operatorname{lt}\left(a, b\right) \Rightarrow \left(\operatorname{le}\left(b, 6 \cdot \operatorname{card}\left(K\right) + 1\right) \Rightarrow \operatorname{sum}\left(\operatorname{Ico}\left(a, b\right), w\right) \ne (0,0)\right)\right) \land \operatorname{sum}\left(\operatorname{range}\left(6 \cdot \operatorname{card}\left(K\right) + 1\right), w\right) = (0,u)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Sequenceability/CharacteristicSevenDetour.exists_characteristic_seven_relative_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is (Fin(6) times K) plus two endpoints. The inverse base permutation has four distinct marked cycles represented by headOne, headTwo, target and source. The original FiniteEndpointPairing.first_visit_reattach and same_cycle_of_first_visit interfaces identify the repaired marked return; FiniteBandSwitch.same_cycle_perm_congr transports its explicit four-cycle. Every base inverse edge connects points of the repaired orbit, proving whole-carrier connectivity rather than only the endpoint closing edge.

The label reindexing is swap(predecessorOne,source) times swap(predecessorTwo,source). It fixes target and permutes all other tails. Thus the two removed full vector labels are reassigned to predecessorTwo and source, while predecessorOne receives (0,u). Removing target deletes exactly (0,-u). The resulting label map is bijective onto the nonzero columns together with (0,u).

N=6 card(K)+1. Restrict(v,Fin(N+1)) and restrict(w,Fin(N)) are the bounded vertex and label lists. Interior(v,N-1) means i maps to v(i+1) on Fin(N-1), and boundedPrefixes(w,N+1) includes both the empty and full prefix. The one-cycle enumeration starts at source and ends at target because Q(target)=source. Telescoping identifies every prefix with its vertex and every interval with the difference of two distinct vertices, including the full interval.

No extension-degree or primitive-generator exception is assumed. The construction covers both primitive generators of F7. The arbitrary-subset, same-M and original-coordinate parent problem is outside this theorem.

## References

- Truth anchor: `D5/S1/Words/Sequenceability/CharacteristicSevenDetour.exists_characteristic_seven_lift`
- Truth anchor: `D5/S1/Words/Sequenceability/CharacteristicSevenDetour.exists_characteristic_seven_relative_path`
- Truth anchor: `D5/S1/Words/Sequenceability/CharacteristicSevenDetour.six_column_splice_seams`
- Dependency: [D5/S1/Words/Sequenceability/RowOrbitLift](RowOrbitLift.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch](../../../S3/Combinatorics/PerfectMatchings/FiniteBandSwitch.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing](../../../S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers](../../../S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.md)
