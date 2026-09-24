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

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right), a \in \operatorname{Edge}\left(\operatorname{product}\left(U, V\right)\right),\; \operatorname{join}\left(U, V, \operatorname{first}\left(\operatorname{split}\left(U, V, a\right)\right), \operatorname{second}\left(\operatorname{split}\left(U, V, a\right)\right), \operatorname{splitBoundary}\left(U, V, a\right)\right) = a$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.join_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse total-label fiber equivalence recovers the original outside endpoints, total label and parallel-edge number.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.join_split`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedGroupOverlap.split_join`
- Dependency: [D5/S3/ConceptDynamics/Coding/EquivariantOverlapRecoding](EquivariantOverlapRecoding.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier](RectangularNilpotenceBarrier.md)
