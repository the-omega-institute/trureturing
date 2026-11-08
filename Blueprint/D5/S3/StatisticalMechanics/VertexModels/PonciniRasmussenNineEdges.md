# Reindexing the generator edges

## Abstract

Reindexing the generator edges

Incoming and outgoing lists contain pairs (target,source), with source embedded in Fin(8192). Multiplicities remain present. Kernel reduction checks the sorted source blocks and their successive merges. The structural merge evaluator agrees with List.merge, whose permutation theorem transfers the exact finite sum. The calculation applies to every additive commutative group.

**Definition 1.1 (incoming).**

$$\forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{incoming}\left(i\right) = \operatorname{get}\left(rows, \operatorname{val}\left(i\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.incoming` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed binary tree contains the same incoming source lists used by sparseHamiltonian.

**Theorem 1.2 (sparseHamiltonian_eq).**

$$\forall v \in \operatorname{Function}\left(\operatorname{Fin}\left(8192\right), Int\right),\; \forall i \in \operatorname{Fin}\left(8192\right),\; \operatorname{sparseHamiltonian}\left(v, i\right) = \operatorname{Negate}\left(\operatorname{FoldLeft}\left(\operatorname{incoming}\left(i\right), \operatorname{AddIncomingCoefficient}\left(v, 8192\right), 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.sparseHamiltonian_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AddIncomingCoefficient(s,j) is s+v(j modulo 8192).

**Definition 1.3 (incomingEdges).**

$$incomingEdges = \operatorname{FlatMap}\left(\operatorname{finRange}\left(4862\right), \operatorname{IncomingTargetSourcePairs}\left(incoming, 8192\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.incomingEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For target t, map every source s in incoming(t) to (t,s modulo 8192).

**Definition 1.4 (outgoingEdges).**

$$outgoingEdges = \operatorname{FlatMap}\left(\operatorname{finRange}\left(4862\right), \operatorname{FilterMap}\left(\operatorname{finRange}\left(8\right), NonzeroTransitionTargetSource\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.outgoingEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each source s and generator g, include (transition(g,s),s) precisely when the transition is below 4862.

**Theorem 1.5 (edges_perm).**

$$\operatorname{Perm}\left(incomingEdges, outgoingEdges\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.edges_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The edge multiset is preserved exactly.

**Theorem 1.6 (sparse_sum).**

$$\forall A \in Type,\; [\operatorname{AddCommGroup}\left(A\right)] \forall b \in \operatorname{Function}\left(\operatorname{Fin}\left(4862\right), A\right),\; \forall v \in \operatorname{Function}\left(\operatorname{Fin}\left(8192\right), Int\right),\; \operatorname{Sum}\left(t, \operatorname{Fin}\left(4862\right), \operatorname{IntegerSMul}\left(\operatorname{sparseHamiltonian}\left(v, \operatorname{CastFin}\left(t, 8192\right)\right), \operatorname{b}\left(t\right)\right)\right) = \operatorname{Negate}\left(\operatorname{Sum}\left(s, \operatorname{Fin}\left(4862\right), \operatorname{Sum}\left(g, \operatorname{Fin}\left(8\right), \operatorname{IfLess}\left(\operatorname{val}\left(\operatorname{transition}\left(g, s\right)\right), 4862, \operatorname{IntegerSMul}\left(\operatorname{v}\left(\operatorname{CastFin}\left(s, 8192\right)\right), \operatorname{b}\left(\operatorname{transition}\left(g, s\right)\right)\right), 0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.sparse_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integer scalar multiplication distributes over the finite incoming rows. The edge permutation gives the equality in any additive commutative group.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.edges_perm`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.incoming`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.incomingEdges`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.outgoingEdges`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.sparseHamiltonian_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineEdges.sparse_sum`
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineDiagrams](PonciniRasmussenNineDiagrams.md)
- Dependency: [D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHornerData](PonciniRasmussenNineHornerData.md)
