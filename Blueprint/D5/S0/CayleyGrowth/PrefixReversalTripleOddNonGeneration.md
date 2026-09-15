# Prefix Reversal Triple Odd Non Generation

## Abstract

Three prefix reversals of small total length generate a proper subgroup at odd degree.

**Theorem 1.1 (The exchanged pairs are few).**

Lean statement: `D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.auxiliaryGraph_edge_bound`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.auxiliaryGraph_edge_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Collect into one graph on the positions every pair that one of the three prefix reversals exchanges. A pair coming from the reversal of length L has endpoints summing to L minus one in zero based indexing, so pairs from different lengths are never equal and the three families are disjoint. Each length contributes at most its half rounded down, so the graph has at most the sum of the three halved lengths.

**Theorem 1.2 (The generated subgroup fixes every component).**

Lean statement: `D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.tripleSubgroup_preserves_components`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.tripleSubgroup_preserves_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the three reversals sends a position either to itself or to its partner across a single edge of that graph, so it leaves the connected component of every position unchanged. The property is closed under product and inverse and holds at the identity, so by induction on the generated subgroup every one of its elements leaves every component unchanged.

**Theorem 1.3 (The odd case of the triangular non-generating region).**

Lean statement: `D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.odd_prefix_reversal_triple_ne_top`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.odd_prefix_reversal_triple_ne_top` (`✓ std3`). ∎

*Citation.* Saúl A. Blanco, Mikhail P. Golubyatnikov, Elena V. Konstantinova, Natalia V. Maslova, Luka A. Nikiforov (2025). *Generating the symmetric group by three prefix reversals*. DOI: [10.48550/arXiv.2511.16959](https://doi.org/10.48550/arXiv.2511.16959).

*Commentary.*

The literature note attests the conjecture, not this theorem. Let the three lengths satisfy two at most k, k below m, m below n, let n be odd, and let m plus k be less than n minus one. Halving and rounding down is superadditive, so the halved m plus the halved k is at most the halved sum, which is at most one less than the halved n. The graph therefore has at most n minus two edges, while a connected graph on n vertices has at least n minus one. So the graph is disconnected. Taking a position outside the component of a fixed one, the transposition exchanging them moves that component and hence lies outside the generated subgroup, which is therefore proper. This is the first clause of the conjecture for odd degree; the even clause needs a different argument and is not proved here.

## References

- Truth anchor: `D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.auxiliaryGraph_edge_bound`
- Truth anchor: `D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.odd_prefix_reversal_triple_ne_top`
- Truth anchor: `D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration.tripleSubgroup_preserves_components`
