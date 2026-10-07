# Counted group-labelled overlap codes

## Abstract

Each total group label has its own finite path fiber. Splitting those fibers transports both numbered histories and their group coordinates.

**Theorem 1.1 (Recover both labelled half-edges).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right), a \in \operatorname{Edge}\left(U\right), b \in \operatorname{Edge}\left(V\right), h \in \operatorname{target}\left(a\right) = \operatorname{source}\left(b\right),\; \operatorname{split}\left(U, V, \operatorname{join}\left(U, V, a, b, h\right)\right) = \operatorname{pair}\left(a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.split_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The total-label fiber equivalence retains the middle vertex, both labels and both parallel-edge numbers, so splitting after joining recovers the full pair.

**Theorem 1.2 (Recover the original labelled edge).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right), a \in \operatorname{Edge}\left(\operatorname{product}\left(U, V\right)\right),\; \operatorname{join}\left(U, V, \operatorname{first}\left(\operatorname{split}\left(U, V, a\right)\right), \operatorname{second}\left(\operatorname{split}\left(U, V, a\right)\right)\right) = a$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.join_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The split half-edges have matching middle endpoints; their equality proof is implicit in the displayed join. The inverse total-label fiber equivalence recovers the original outside endpoints, total label and parallel-edge number.

**Definition 1.3 (Every actual edge coordinate).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right), M \in \operatorname{GroupMat}\left(H, n, m\right),\; \operatorname{Equiv}\left(\operatorname{Edge}\left(M\right), \operatorname{SigmaEdgeCoordinates}\left(M\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.edgeCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

edgeCoordinates sends an edge to the dependent tuple of source, target, group label and copy number, and reconstructs those exact four fields. The number type is Fin(coeff(M[source,target],label)); empty coefficient fibers contribute no edge. edgeFintype enumerates this complete sigma type and edgeDecidableEq transports decidable coordinate equality. No parallel edges are identified.

**Definition 1.4 (The prescribed lexicographic rank).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right), order \in \operatorname{LinearOrder}\left(H\right), i \in \operatorname{Fin}\left(n\right), k \in \operatorname{Fin}\left(n\right), g \in H,\; \operatorname{Equiv}\left(\operatorname{Fin}\left(\operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{product}\left(U, V\right), i, k\right), g\right)\right), \operatorname{Fiber}\left(U, V, i, k, g\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.orderedFiberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For fixed outside endpoints i,k and total label g, rank the dependent fiber by intermediate j, first label alpha in the supplied total order, first copy cU, then second copy cV. The second label is alpha inverse times g. The nested sigma and product orders are lexicographic. The cardinality is reused from fiberEquiv, but the map is the pinned increasing orderIsoFinOfCardEq, not its arbitrary enumeration. Empty fibers are included with cardinality zero. This is a consumed rank adapter, not a novel conjugacy theorem.

**Definition 1.5 (orderedSplit).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right), order \in \operatorname{LinearOrder}\left(H\right), a \in \operatorname{Edge}\left(\operatorname{product}\left(U, V\right)\right),\; \operatorname{Prod}\left(\operatorname{Edge}\left(U\right), \operatorname{Edge}\left(V\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.orderedSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

orderedSplit reads the original total-label numbered edge through orderedFiberEquiv and returns the actual two half-edges. It retains both outside endpoints, the shared middle vertex, first label alpha, second label alpha inverse times the original label, and both copy numbers.

**Definition 1.6 (orderedJoin).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right), order \in \operatorname{LinearOrder}\left(H\right), a \in \operatorname{Edge}\left(U\right), b \in \operatorname{Edge}\left(V\right), h \in \operatorname{target}\left(a\right) = \operatorname{source}\left(b\right),\; \operatorname{Edge}\left(\operatorname{product}\left(U, V\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.orderedJoin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

orderedJoin uses the inverse prescribed fiber rank on two actual composable half-edges. Its label is the ordered product of the first and second labels. Its endpoints and number are those of this same ordered rank.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.edgeCoordinates`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.join_split`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.orderedFiberEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.orderedJoin`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.orderedSplit`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.split_join`
- Dependency: [D5/S3/ConceptDynamics/Coding/EquivariantOverlapRecoding](EquivariantOverlapRecoding.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier](RectangularNilpotenceBarrier.md)
