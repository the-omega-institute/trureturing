# Characteristic-seven six-column detour

## Abstract

Six-column affine group action and the overlapping two-head characteristic-seven splice.

The generic row-return theorem supplies the affine orbit calculation. This document records the genuinely new six-phase lift in ZMod(7), its exact inventories, and exact vector-label conservation for the overlapping endpoint splice. These are formal proofs of the stated construction, with no claim of literature novelty.

**Theorem 1.1 (Exact six-phase cycles and inventories).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall f \in \operatorname{Field}\left(K\right),\; \forall finite \in \operatorname{Finite}\left(K\right),\; \forall char \in \operatorname{CharP}\left(K, 7\right),\; \forall c \in K,\; \exists r \in \operatorname{Units}\left(K\right),\; \operatorname{coe}\left(r\right) + 1 \ne 0 \land \left(\left(\forall v \in \operatorname{Fin}\left(6\right) \times K,\; \forall w \in \operatorname{Fin}\left(6\right) \times K,\; \operatorname{SameCycle}\left(\operatorname{lift}\left(r, c\right), v, w\right) \Leftrightarrow \left(\operatorname{initialRow}\left(v\right) = c \Leftrightarrow \operatorname{initialRow}\left(w\right) = c\right)\right) \land \left(\operatorname{BijOn}\left(\operatorname{edgeLabel}\left(r, c\right), \operatorname{univ}\left(\right), \{v:\operatorname{ZMod}\left(7\right) \times K\mid\operatorname{fst}\left(v\right) \ne 0\}\right) \land \left(\operatorname{BijOn}\left(\operatorname{vertex}\left(\right), \operatorname{univ}\left(\right), \{v:\operatorname{ZMod}\left(7\right) \times K\mid\operatorname{fst}\left(v\right) \ne 0\}\right) \land \left(\forall h \in K,\; \left(\operatorname{lift}\left(r, c\right)^{6}\right)\left((0,h)\right) = (0,\operatorname{rowReturn}\left(r, c\right)\left(h\right))\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.exists_characteristic_seven_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A primitive unit gives the two affine row cycles. The six first-coordinate differences are the nonzero elements of F7, and each row-coordinate map is invertible. The vertex and label BijOn statements therefore cover every nonzero column exactly once over arbitrary finite extensions.

**Theorem 1.2 (Overlapping endpoint seams).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall f \in \operatorname{Field}\left(K\right),\; \forall char \in \operatorname{CharP}\left(K, 7\right),\; \forall r \in \operatorname{Units}\left(K\right),\; \forall u \in K,\; u \ne 0 \Rightarrow \left(\operatorname{coe}\left(r\right) + 1 \ne 0 \Rightarrow \left(\operatorname{splice}\left(r, u\right)\left(\operatorname{predecessorOne}\left(r, u\right)\right) = \operatorname{headTwo}\left(r, u\right) \land \left(\operatorname{splice}\left(r, u\right)\left(\operatorname{predecessorTwo}\left(r, u\right)\right) = \operatorname{target}\left(\right) \land \left(\operatorname{splice}\left(r, u\right)\left(\operatorname{source}\left(\right)\right) = \operatorname{headOne}\left(r, u\right) \land \left(\operatorname{splice}\left(r, u\right)\left(\operatorname{target}\left(\right)\right) = \operatorname{source}\left(\right) \land \left(\operatorname{vertexWithEndpoints}\left(u, \operatorname{headTwo}\left(r, u\right)\right) - \operatorname{vertexWithEndpoints}\left(u, \operatorname{predecessorOne}\left(r, u\right)\right) = (0,u) \land \left(\operatorname{vertexWithEndpoints}\left(u, \operatorname{target}\left(\right)\right) - \operatorname{vertexWithEndpoints}\left(u, \operatorname{predecessorTwo}\left(r, u\right)\right) = (2,2 \cdot \operatorname{alpha}\left(r, u\right)) \land \left(\operatorname{vertexWithEndpoints}\left(u, \operatorname{headOne}\left(r, u\right)\right) - \operatorname{vertexWithEndpoints}\left(u, \operatorname{source}\left(\right)\right) = (3,\operatorname{alpha}\left(r, u\right)) \land \operatorname{vertexWithEndpoints}\left(u, \operatorname{source}\left(\right)\right) - \operatorname{vertexWithEndpoints}\left(u, \operatorname{target}\left(\right)\right) = (0,-u)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.six_column_splice_seams` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With alpha=(r+1)u/(3r), c=-alpha and beta=u-alpha, the two heads have initial rows c and c+u. The predecessor equations and all four actual seam labels are retained before the closing target-to-source edge is deleted.

**Theorem 1.3 (Generating-unit cycle criterion).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall f \in \operatorname{Field}\left(K\right),\; \forall finite \in \operatorname{Finite}\left(K\right),\; \forall r \in \operatorname{Units}\left(K\right),\; \left(\forall z \in \operatorname{Units}\left(K\right),\; \exists n \in \operatorname{Nat}\left(\right),\; r^{n} = z\right) \Rightarrow \left(\forall c \in K,\; \forall v \in \operatorname{Fin}\left(6\right) \times K,\; \forall w \in \operatorname{Fin}\left(6\right) \times K,\; \operatorname{SameCycle}\left(\operatorname{lift}\left(r, c\right), v, w\right) \Leftrightarrow \left(\operatorname{initialRow}\left(v\right) = c \Leftrightarrow \operatorname{initialRow}\left(w\right) = c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.lift_same_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every field with finite carrier, every generating unit r, every c and all two vertices, the six-phase lift has the same-cycle relation exactly when their initial rows are simultaneously equal or unequal to c. Generating means that every unit is a natural power of r. CharacteristicSevenRelativePath uses this criterion to identify the distinct marked base cycles.

**Theorem 1.4 (Nonzero primitive affine coefficient).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall f \in \operatorname{Field}\left(K\right),\; \forall char \in \operatorname{CharP}\left(K, 7\right),\; \forall r \in \operatorname{Units}\left(K\right),\; \left(\forall z \in \operatorname{Units}\left(K\right),\; \exists n \in \operatorname{Nat}\left(\right),\; r^{n} = z\right) \Rightarrow \operatorname{coe}\left(r\right) + 1 \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.generator_add_one_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every characteristic-seven field, a unit generating all units cannot equal minus one: the powers of minus one omit the unit two. There is no finiteness assumption in this conditional statement. The lift and the final path use the result to invert their label coefficient, including both primitive units of F7.

**Theorem 1.5 (Exact off-target vector-label inventory).**

$$\forall K \in \operatorname{Type}\left(\right),\; \forall f \in \operatorname{Field}\left(K\right),\; \forall finite \in \operatorname{Finite}\left(K\right),\; \forall char \in \operatorname{CharP}\left(K, 7\right),\; \forall r \in \operatorname{Units}\left(K\right),\; \forall u \in K,\; u \ne 0 \Rightarrow \left(\operatorname{coe}\left(r\right) + 1 \ne 0 \Rightarrow \operatorname{BijOn}\left(\operatorname{successorLabel}\left(r, u\right), \{x \mid x \ne \operatorname{target}\left(\right)\}, \{z \mid \operatorname{fst}\left(z\right) \ne 0 \lor z = (0,u)\}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.splice_labels_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite characteristic-seven field, every unit r with r+1 nonzero, and every nonzero u, successorLabel(r,u)(x) means vertexWithEndpoints(u)(splice(r,u)(x)) minus vertexWithEndpoints(u)(x). Its restriction to tails different from target is bijective onto all nonzero columns together with (0,u). The exact tail reindexing fixes target and redistributes the three changed labels, so deleting target removes exactly (0,-u). The path enumeration consumes this entire vector inventory.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.exists_characteristic_seven_lift`
- Truth anchor: `D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.generator_add_one_ne_zero`
- Truth anchor: `D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.lift_same_cycle`
- Truth anchor: `D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.six_column_splice_seams`
- Truth anchor: `D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.splice_labels_bijective`
- Dependency: [D5/S1/Words/Sequenceability/RowOrbitLift](../../../S1/Words/Sequenceability/RowOrbitLift.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch](../PerfectMatchings/FiniteBandSwitch.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing](../PerfectMatchings/FiniteEndpointPairing.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers](../PerfectMatchings/FiniteReturnTowers.md)
