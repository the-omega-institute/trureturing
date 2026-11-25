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

**Definition 1.3 (Source Sample).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), (\mathit{SourceSample} n k : \mathit{Type}) = \mathit{Equiv}.\mathit{Perm} (\mathit{Fin} n) \times \mathit{CayleyReduction}.\mathit{Colored} (\mathit{Fin} n) (\mathit{ZMod} k)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.SourceSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.4 (Inst Is Probability Measure Uniform Of Nonempty Of Measurable Singleton Class).**

$$\forall (X: \mathit{Type}), [\mathit{Finite} X] [\mathit{Nonempty} X] [\mathit{MeasurableSpace} X] [\mathit{MeasurableSingletonClass} X] \mathit{MeasureTheory}.\mathit{IsProbabilityMeasure} (\mathit{uniform} X)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.instIsProbabilityMeasureUniformOfNonemptyOfMeasurableSingletonClass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.5 (Permutation Measurable Singleton).**

$$\forall (n: \mathbb{N}), \mathit{MeasurableSingletonClass} (\mathit{Equiv}.\mathit{Perm} (\mathit{Fin} n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.permutationMeasurableSingleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.6 (Permutation Measurable Space).**

$$\forall (n: \mathbb{N}), (\mathit{permutationMeasurableSpace} n : \mathit{MeasurableSpace} (\mathit{Equiv}.\mathit{Perm} (\mathit{Fin} n))) = \operatorname{top}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.permutationMeasurableSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.7 (Source Measure).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), [\mathit{NeZero} k] (\mathit{sourceMeasure} n k : \mathit{MeasureTheory}.\mathit{Measure} (\mathit{CayleyTreeProbability}.\mathit{SourceSample} n k)) = \mathit{uniform} (\mathit{CayleyTreeProbability}.\mathit{SourceSample} n k)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.sourceMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.8 (Tree Measurable Singleton).**

$$\forall (n: \mathbb{N}), \mathit{MeasurableSingletonClass} (\mathit{CayleyProbe}.\mathit{Tree} (\mathit{Fin} n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.treeMeasurableSingleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.9 (Tree Measurable Space).**

$$\forall (n: \mathbb{N}), (\mathit{treeMeasurableSpace} n : \mathit{MeasurableSpace} (\mathit{CayleyProbe}.\mathit{Tree} (\mathit{Fin} n))) = \operatorname{top}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.treeMeasurableSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.10 (Uniform).**

$$\forall (X: \mathit{Type}), [\mathit{Finite} X] [\mathit{MeasurableSpace} X] (\mathit{uniform} X : \mathit{MeasureTheory}.\mathit{Measure} X) = \mathit{have} \mathit{this} := \mathit{Fintype}.\mathit{ofFinite} X; \mathit{MeasureTheory}.\mathit{Measure}.\mathit{uniformOfFinset} \mathit{Finset}.\mathit{univ}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.uniform` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.SourceSample`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.instIsProbabilityMeasureUniformOfNonemptyOfMeasurableSingletonClass`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.microstate_word_law`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.permutationMeasurableSingleton`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.permutationMeasurableSpace`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.sourceMeasure`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.source_occupancy_law`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.treeMeasurableSingleton`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.treeMeasurableSpace`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability.uniform`
- Dependency: [D5/S3/Analytic/Probability/DiscardedOccupancy/NormalLimit](../../../Analytic/Probability/DiscardedOccupancy/NormalLimit.md)
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw](FiniteLaw.md)
