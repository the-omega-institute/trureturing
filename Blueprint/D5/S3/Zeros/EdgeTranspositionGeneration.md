# Edge Transposition Generation

## Abstract

The swaps across the edges of a finite connected graph generate every permutation of its vertices.

**Theorem 1.1 (Connected edge transpositions generate the full symmetric group).**

$$\forall V, G: \operatorname{SimpleGraph}\left(V\right), \operatorname{Finite}\left(V\right) \land \operatorname{Connected}\left(G\right) \Rightarrow \operatorname{closure}\left(\operatorname{edgeTranspositions}\left(G\right)\right) = \operatorname{topSubgroup}\left(\operatorname{Perm}\left(V\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/EdgeTranspositionGeneration.connected_edge_transpositions_generate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a simple graph G, edgeTranspositions(G) is exactly the set of swaps whose two endpoints are adjacent. Graph adjacency supplies the distinct-endpoint condition required of every transposition.

Reachability is unfolded as the reflexive transitive closure of adjacency. Induction along that closure constructs a swap of the two path endpoints inside the generated subgroup, so connectedness makes the subgroup action pretransitive.

The final equality is the direct specialization of Mathlib's closure_of_isSwap_of_isPretransitive. Applying the theorem to the induced graph on any connected component gives the componentwise form. No concrete monodromy graph is asserted to be connected.

## References

- Truth anchor: `D5/S3/Zeros/EdgeTranspositionGeneration.connected_edge_transpositions_generate`
