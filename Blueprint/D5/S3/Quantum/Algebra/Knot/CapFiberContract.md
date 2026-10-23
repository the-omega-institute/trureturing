# Legal-path cap fibers

## Abstract

Legal-path cap fibers.

**Definition 1.1 (Legal-path cap fibers).**

$$\forall L \in \mathit{FiniteDecidableType},\; \forall R \in \operatorname{Relation}\left(L\right),\; \forall q \in \operatorname{Function}\left(L, \mathit{Real}\right),\; \forall s \in L,\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \operatorname{CapFiberGoal}\left(R, q, s, m, M, j\right) \Leftrightarrow \left(\exists N \in \operatorname{NCMatching}\left(m\right),\; \left(\forall k \in \operatorname{Fin}\left(m\right),\; \operatorname{SkipPair}\left(j, \operatorname{Partner}\left(N, k\right)\right) = \operatorname{ReconnectPartner}\left(M, j, \operatorname{SkipPair}\left(j, k\right)\right)\right) \land \left(\forall y \in \operatorname{LegalPath}\left(R, m, s, s\right),\; \left(\operatorname{Partner}\left(M, \operatorname{CastSucc}\left(j\right)\right) = \operatorname{Succ}\left(j\right) \Rightarrow \left(\left(\forall b \in \operatorname{NeighborLabels}\left(R, \operatorname{Apply}\left(y, j\right)\right),\; \operatorname{Compatible}\left(M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \Leftrightarrow \operatorname{Compatible}\left(N, y\right)\right) \land \left(\forall b \in \operatorname{NeighborLabels}\left(R, \operatorname{Apply}\left(y, j\right)\right),\; \operatorname{BoundaryPotential}\left(q, M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \cdot \operatorname{Divide}\left(\operatorname{Apply}\left(q, b\right), \operatorname{Apply}\left(q, \operatorname{Apply}\left(y, j\right)\right)\right) = \operatorname{Square}\left(\operatorname{Divide}\left(\operatorname{Apply}\left(q, b\right), \operatorname{Apply}\left(q, \operatorname{Apply}\left(y, j\right)\right)\right)\right) \cdot \operatorname{BoundaryPotential}\left(q, N, y\right)\right)\right)\right) \land \left(\operatorname{Partner}\left(M, \operatorname{CastSucc}\left(j\right)\right) \ne \operatorname{Succ}\left(j\right) \Rightarrow \left(\left(\operatorname{Compatible}\left(N, y\right) \Leftrightarrow \left(\exists b \in \operatorname{NeighborLabels}\left(R, \operatorname{Apply}\left(y, j\right)\right),\; \operatorname{Compatible}\left(M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \land \left(\forall c \in \operatorname{NeighborLabels}\left(R, \operatorname{Apply}\left(y, j\right)\right),\; \operatorname{Compatible}\left(M, \operatorname{DetourLabels}\left(j, y, c\right)\right) \Rightarrow c = b\right)\right)\right) \land \left(\forall b \in \operatorname{NeighborLabels}\left(R, \operatorname{Apply}\left(y, j\right)\right),\; \operatorname{Compatible}\left(M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \Rightarrow \operatorname{BoundaryPotential}\left(q, M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \cdot \operatorname{Divide}\left(\operatorname{Apply}\left(q, b\right), \operatorname{Apply}\left(q, \operatorname{Apply}\left(y, j\right)\right)\right) = \operatorname{BoundaryPotential}\left(q, N, y\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/Knot/CapFiberContract.CapFiberGoal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FiniteDecidableType denotes any finite label type with decidable equality. NeighborLabels(R,a) is the subtype of labels b satisfying R(a,b); formulas involving such a neighbor use its underlying label. Apply is function evaluation, CastSucc and Succ are the left and right gap inclusions, and Square is the ordinary second power. Fix an arbitrary label relation, real label weights, a root, an adjacent cap and a noncrossing matching. The goal requires a smaller matching with the exact rewiring and both complete cap-fiber laws over the existing rooted LegalPath carrier. The closed law quantifies every neighboring middle label and includes the squared ratio. The nonclosed law requires a unique legal neighbor exactly when the smaller labels are compatible, and the exact potential transport for each compatible lift.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Knot/CapFiberContract.CapFiberGoal`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore](../../../Combinatorics/PerfectMatchings/OrderedMatchingCore.md)
- Dependency: [D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb](../WeightedLegalPathTemperleyLieb.md)
