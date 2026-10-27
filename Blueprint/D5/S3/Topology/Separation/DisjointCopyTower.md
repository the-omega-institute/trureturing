# Disjoint compact copy towers

## Abstract

A tower of nonempty compact sets with two disjoint copies at every step forces disjoint infinite closed homeomorphic subspaces.

X is any Hausdorff space; no compactness of X is assumed. K is a sequence of subsets of X. AllLevelsCompact means that every K(n) is compact, and AllLevelsNonempty means that every K(n) contains a point. DisjointSuccessorCopies means: for every natural n there are ambient subsets A and B contained in K(n), disjoint in X, and homeomorphisms from K(n+1) onto A and B with their actual subtype topologies. No infinitude of the levels or closedness of the copies is supplied as an assumption.

**Theorem 1.1 (A compact binary-copy tower contains two infinite closed copies).**

$$\forall X \in TopologicalSpaceU,\; T2Space\left(X\right) \Rightarrow \left(\forall K \in Function\left(Nat, Set\left(X\right)\right),\; \left(AllLevelsCompact\left(K\right) \land \left(AllLevelsNonempty\left(K\right) \land DisjointSuccessorCopies\left(K\right)\right)\right) \Rightarrow \left(\exists A \in Set\left(X\right),\; \exists B \in Set\left(X\right),\; IsClosed\left(A\right) \land \left(IsClosed\left(B\right) \land \left(Infinite\left(A\right) \land \left(Infinite\left(B\right) \land \left(Disjoint\left(A, B\right) \land Nonempty\left(Homeomorph\left(Subtype\left(A\right), Subtype\left(B\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Separation/DisjointCopyTower.exists_disjoint_infinite_closed_copies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

Suppose some level is finite. Among the finite cardinalities of all finite levels choose the least one, attained at K(j). The first copy gives an injection from K(j+1) into the finite set K(j), hence the next level is finite as well. Nonemptiness of K(j+1) supplies a point in the second copy. Disjointness puts that point outside the first injection's range. Fintype.card_lt_of_injective_of_notMem therefore gives a strictly smaller finite level cardinality, contradicting minimality. This proves that every level is infinite; it does not infer infinitude from nonemptiness alone.

Take the two copies of K(1) inside K(0). They are compact because the respective homeomorphisms are continuous, and therefore closed in the Hausdorff ambient space. Their underlying bijections transfer the established infinitude of K(1). The inverse of the first homeomorphism followed by the second gives a homeomorphism between these disjoint infinite closed sets.

Consequently a Hausdorff space with no two disjoint infinite closed homeomorphic subspaces has no such tower. The tower is the 2DCP configuration in section 1 of arXiv:2607.06808v2.

## References

- Truth anchor: `D5/S3/Topology/Separation/DisjointCopyTower.exists_disjoint_infinite_closed_copies`
