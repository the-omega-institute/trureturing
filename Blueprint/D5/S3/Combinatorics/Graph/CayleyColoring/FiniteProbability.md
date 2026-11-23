# From marked draws to the source probability law

## Abstract

The native move count and literal occupancy have identical distributions in every positive row.

**Theorem 1.1 (Coordinatewise pushforward of the marked word).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), [\operatorname{NeZero}\left(k\right)] \forall (m: \mathbb{N}), 0<n \implies 2 \leq k \implies \operatorname{map}\left(\operatorname{uniform}\left(\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right) \times \operatorname{ZMod}\left(k\right)\right), (w: \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right) \times \operatorname{ZMod}\left(k\right) \mapsto (i: \operatorname{Fin}\left(m\right) \mapsto \operatorname{bin}\left(w\left(i\right)\right)))\right) = \operatorname{literalMeasure}\left(n, k, m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.microstate_word_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The marked word is uniform on functions from the throw coordinates to pairs of a bin and a color mark. This is the product of uniform pair measures. Pushforward along the coordinatewise bin map therefore yields the product of the one-throw laws. The result includes the empty word.

**Theorem 1.2 (Equality of source and occupancy distributions).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), [\operatorname{NeZero}\left(k\right)] 0<n \implies 2 \leq k \implies \forall (K: Type), \forall (e: \operatorname{Embedding}\left(\operatorname{ZMod}\left(k\right), K\right)), \operatorname{Nonempty}\left((s: \operatorname{Colored}\left(\operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(k\right)\right)) \to \operatorname{FreePolicy}\left(K, \operatorname{graph}\left(s\right)\right)\right) \implies \operatorname{IdentDistrib}\left((t: \operatorname{SourceSample}\left(n, k\right) \mapsto \operatorname{realCast}\left(\operatorname{sourceCount}\left(e, t\right)\right)), \operatorname{literalCount}\left(n, n - 1\right), \operatorname{sourceMeasure}\left(n, k\right), \operatorname{literalMeasure}\left(n, k, n - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.source_occupancy_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

The source samples a root, a native labeled tree, and each initial color independently and uniformly. A uniform ranking supplies the conditional law of the legal sequential histories for any valid free-color policy. The native all-size count law is converted to equal singleton masses, and reindexing the non-anchor coordinates preserves exactly which ordinary bins appear.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.microstate_word_law`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.source_occupancy_law`
- Dependency: [D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit](../../../Analytic/Probability/DiscardedOccupancy/NormalLimit.md)
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw](FiniteLaw.md)
