# Prefix Reversal Triple Even Non Generation

## Abstract

At even degree the three prefix reversals split the positions into two exchanged halves.

**Theorem 1.1 (Root path parity differs across an edge by its weight).**

Lean statement: `D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration.rootParity_edge`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration.rootParity_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Weight one the edges coming from the longest reversal and zero the others, and label each position by the sum of the weights along its unique path from a fixed root. For any edge, the two labels differ by the weight of that edge. Append the edge to the root path of one endpoint: either the result is a path, and uniqueness makes it the root path of the other endpoint, or the other endpoint already lies on the first path, and uniqueness makes the initial segment its root path and the remaining segment the single edge. The two cases give the same equation over the two element field.

**Theorem 1.2 (At even degree the longest reversal flips every label).**

Lean statement: `D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration.longest_reversal_exchanges`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration.longest_reversal_exchanges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The longest reversal has no fixed position when the degree is even, so every position lies on one of its edges, and those edges carry weight one. By the preceding equation the label of a position and the label of its image differ by one. The two shorter reversals exchange only weight zero pairs and fix everything else, so they leave every label unchanged.

**Theorem 1.3 (The even clause of the triangular non-generating region).**

Lean statement: `D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration.even_prefix_reversal_triple_ne_top`

*Proof.* Machine-checked in Lean as `D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration.even_prefix_reversal_triple_ne_top` (`✓ std3`). ∎

*Citation.* Saúl A. Blanco, Mikhail P. Golubyatnikov, Elena V. Konstantinova, Natalia V. Maslova, Luka A. Nikiforov (2025). *Generating the symmetric group by three prefix reversals*. DOI: [10.48550/arXiv.2511.16959](https://doi.org/10.48550/arXiv.2511.16959).

*Commentary.*

The literature note attests the conjecture, not this theorem. Let the three lengths satisfy two at most k, k below m, m below n, let n be even, and let m plus k be less than n. If the position graph is disconnected the odd-case development already gives properness. Otherwise the edge bound and connectivity force exactly n minus one edges, so the graph is a tree and the root path labelling applies. Every element of the generated subgroup either fixes both label classes or exchanges them, since that property holds of the three reversals and is closed under product and inverse. The longest reversal is a bijection between the classes, so each has half the positions and both have at least two. A transposition taking one position of the zero class to the one class sends that class to a set which is neither, so it lies outside the subgroup. Together with the odd case this settles both clauses of the conjecture, the first clause at even degree following from the second.

## References

- Truth anchor: `D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration.even_prefix_reversal_triple_ne_top`
- Truth anchor: `D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration.longest_reversal_exchanges`
- Truth anchor: `D5/S0/CayleyGrowth/PrefixReversalTripleEvenNonGeneration.rootParity_edge`
- Dependency: [D5/S0/CayleyGrowth/PrefixReversalTripleOddNonGeneration](PrefixReversalTripleOddNonGeneration.md)
