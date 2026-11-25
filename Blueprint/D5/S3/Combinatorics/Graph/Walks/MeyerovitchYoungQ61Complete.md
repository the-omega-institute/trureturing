# The complete matrix reduction for Meyerovitch–Young Question 6.1

## Abstract

Complete min-plus matrices preserve the finite-horizon value of primitive graph games.

In the game of Meyerovitch and Young, Alice chooses a legal edge word of a fixed length, and Bob minimizes its paired edge payoff over all Bob walks of that length. Both endpoints of each walk are free. The reduction applies to arbitrary finite nonempty primitive directed multigraphs and to costs in any linearly ordered commutative ring, including the field in Question 6.1. https://arxiv.org/html/2603.21449v1#S6.Thmlemma1

**Theorem 1.1 (Exact word scores and the original maximizing walks).**

$$\forall V \in \mathrm{Type}, E \in \mathrm{Type}, W \in \mathrm{Type}, F \in \mathrm{Type}, K \in \mathrm{Type},\; [\mathrm{Finite}\left(V\right)] [\mathrm{Nonempty}\left(V\right)] [\mathrm{Finite}\left(E\right)] [\mathrm{Finite}\left(W\right)] [\mathrm{Nonempty}\left(W\right)] [\mathrm{Finite}\left(F\right)] [\mathrm{CommRing}\left(K\right)] [\mathrm{LinearOrder}\left(K\right)] [\mathrm{IsStrictOrderedRing}\left(K\right)] \forall X \in \mathrm{EdgeGraph}\left(V, E\right),\; \forall Y \in \mathrm{EdgeGraph}\left(W, F\right),\; \forall dX \in \mathrm{Nat},\; \forall dY \in \mathrm{Nat},\; \forall hX \in \mathrm{ConnectsAt}\left(X, dX + 1\right),\; \forall hY \in \mathrm{ConnectsAt}\left(Y, dY + 1\right),\; \forall p \in E \to \left(F \to K\right),\; \exists A \in E \to \mathrm{Matrix}\left((W \times V), (W \times V), K\right),\; \exists C \in K,\; (0 < C) \land ((\forall a \in \mathrm{List}\left(E\right),\; \mathrm{matrixMinimum}\left(A, a\right) + \mathrm{boundary}\left(V, C, \mathrm{length}\left(a\right)\right) = \mathrm{freeMinimum}\left(Y, dY, hY, p, a\right) - C \cdot \mathrm{badJoins}\left(X, a\right)) \land (\forall n \in \mathrm{Nat},\; \exists m \in K,\; (\mathrm{IsGreatest}\left(\{z: K \mid \exists a \in \mathrm{List}\left(E\right),\; (\mathrm{length}\left(a\right) = n) \land ((\mathrm{Legal}\left(X, a\right)) \land (\mathrm{freeMinimum}\left(Y, dY, hY, p, a\right) = z))\}, m\right)) \land ((\mathrm{IsGreatest}\left(\{z: K \mid \exists a \in \mathrm{List}\left(E\right),\; (\mathrm{length}\left(a\right) = n) \land (\mathrm{matrixMinimum}\left(A, a\right) = z)\}, m - \mathrm{boundary}\left(V, C, n\right)\right)) \land (\forall a \in \mathrm{List}\left(E\right),\; (\mathrm{length}\left(a\right) = n) \Rightarrow ((\mathrm{matrixMinimum}\left(A, a\right) + \mathrm{boundary}\left(V, C, n\right) = m) \Leftrightarrow ((\mathrm{Legal}\left(X, a\right)) \land (\mathrm{freeMinimum}\left(Y, dY, hY, p, a\right) = m)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete.finite_horizon_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix family has one matrix per Alice edge, with rows and columns indexed by Bob's vertex and a freely chosen Alice vertex. The free-endpoint matrix score is the minimum entry sum over complete vertex walks. Adding the boundary charge gives the original Bob minimum minus C times the number of incompatible joins. The charge is zero for the empty word and for a singleton Alice vertex set, and is C otherwise.

For each Bob response in the lifted graph, setting the exit register to the current Alice edge's target saves an exit charge larger than the entry penalty it can affect at the next step. The initial register is free, so its minimum contribution gives precisely the common boundary charge. A legal original Bob walk lifts with those registers and attains the penalized score.

Fix a connector of common length for every pair of Alice vertices. Scan the Alice word and copy each compatible edge. At an incompatible join replace a connector-length block with a walk to the original terminal vertex of the block. Replace a final short suffix with a walk of its own length. Each replacement begins at an original incompatible join. Against the same Bob response its loss is bounded by the connector length times the payoff range. Choosing C above that bound makes any illegal word strictly worse than its repair.

For each ordered pair of lifted Bob vertices, minimize over its parallel edges. Give missing pairs a common cost above the largest original cost plus the connector length minus one times the cost range. Any minimum using a missing pair admits a strictly cheaper connector-length replacement with the same endpoints. For a shorter horizon, any original Bob walk of that length gives a strictly cheaper response because endpoints are free.

**Theorem 1.2 (Attainment and lower bound for the matrix minimum).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete.matrixMinimum_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete.matrixMinimum_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a matrix family over a linearly ordered commutative ring on a finite nonempty vertex set, each word has a complete walk whose entry sum is the matrix minimum. The walk has the length of the word, and the same minimum bounds the entry sum of every complete walk of that length from below.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete.finite_horizon_reduction`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MeyerovitchYoungQ61Complete.matrixMinimum_spec`
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierGraph](../LayeredCirculation/SupplierGraph.md)
