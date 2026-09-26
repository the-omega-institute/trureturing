# Counted edges and overlap conjugacy

## Abstract

A nonnegative matrix records numbered parallel edges. Lexicographic fiber ranks split and reassemble each product edge.

**Theorem 1.1 (Recover both numbered half-edges).**

$$\forall n \in Nat, m \in Nat, U \in \operatorname{CountMat}\left(n, m\right), V \in \operatorname{CountMat}\left(m, n\right), a \in \operatorname{Edge}\left(U\right), b \in \operatorname{Edge}\left(V\right), h \in \operatorname{target}\left(a\right) = \operatorname{source}\left(b\right),\; \operatorname{split}\left(U, V, \operatorname{join}\left(U, V, a, b, h\right)\right) = \operatorname{pair}\left(a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedMatrixOverlap.split_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product edge number is the lexicographic rank of its middle vertex and both factor-edge numbers. The proved finite-fiber count supplies the increasing rank equivalence. Splitting after joining therefore recovers the full pair, including parallel-edge identity.

**Theorem 1.2 (Recover the original matrix edge).**

$$\forall n \in Nat, m \in Nat, U \in \operatorname{CountMat}\left(n, m\right), V \in \operatorname{CountMat}\left(m, n\right), a \in \operatorname{Edge}\left(\operatorname{product}\left(U, V\right)\right),\; \operatorname{join}\left(U, V, \operatorname{first}\left(\operatorname{split}\left(U, V, a\right)\right), \operatorname{second}\left(\operatorname{split}\left(U, V, a\right)\right), \operatorname{splitBoundary}\left(U, V, a\right)\right) = a$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedMatrixOverlap.join_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse ordered finite-fiber equivalence recovers the original numbered edge. The outside endpoints are unchanged in both constructions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedMatrixOverlap.join_split`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedMatrixOverlap.split_join`
- Dependency: [D5/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy](BipartiteOverlapConjugacy.md)
