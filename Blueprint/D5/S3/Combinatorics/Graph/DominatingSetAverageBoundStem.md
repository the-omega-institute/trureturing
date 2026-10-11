# Stem-block counting for dominating sets

## Abstract

Stem blocks group a stem with all its leaf neighbours. The local counting estimate is Lemma 2.6 of Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475. Distinct blocks are disjoint, with the two endpoint descriptions of a two-leaf component identified.

**Definition 1.1 (Stem block).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)]\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall s \in V,\; \operatorname{stemBlock}\left(G, s\right) = \operatorname{insert}\left(s, \operatorname{leafNeighbors}\left(G, s\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.stemBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The block is the stem together with all its leaf neighbours.

**Definition 1.2 (Stem substitution).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)]\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall s \in V,\; \forall S \in \operatorname{Finset}\left(V\right),\; \forall T \in \operatorname{Finset}\left(V\right),\; \operatorname{stemSwap}\left(G, s, S, T\right) = \operatorname{union}\left(\operatorname{insert}\left(s, \operatorname{sdiff}\left(S, \operatorname{leafNeighbors}\left(G, s\right)\right)\right), T\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.stemSwap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replace every selected leaf neighbour by the stem and a chosen subset of its leaves.

**Theorem 1.3 (Substitution preserves domination).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)]\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall s \in V,\; \forall S \in \operatorname{Finset}\left(V\right),\; \forall T \in \operatorname{Finset}\left(V\right),\; \operatorname{IsDominating}\left(G, S\right) \Rightarrow \operatorname{IsDominating}\left(G, \operatorname{stemSwap}\left(G, s, S, T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.stemSwap_dominating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inserted stem dominates all removed leaves. Any other vertex formerly dominated by a removed leaf is its stem.

**Definition 1.4 (Distinct stem blocks).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)]\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{stemBlocks}\left(G\right) = \operatorname{image}\left(\operatorname{stemBlock}\left(G\right), \{s \in V | \operatorname{Nonempty}\left(\operatorname{leafNeighbors}\left(G, s\right)\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.stemBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the image of the stems under the block map. Equal two-vertex blocks occur once.

**Theorem 1.5 (Distinct blocks are disjoint).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)]\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall B \in \operatorname{Finset}\left(V\right),\; \forall C \in \operatorname{Finset}\left(V\right),\; \left(B \in \operatorname{stemBlocks}\left(G\right) \land \left(C \in \operatorname{stemBlocks}\left(G\right) \land B \ne C\right)\right) \Rightarrow \operatorname{Disjoint}\left(B, C\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.stemBlocks_pairwiseDisjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A leaf has only one neighbour. Overlapping blocks either have the same stem or are the same component consisting of two adjacent leaves.

**Definition 1.6 (Active dominating-set family).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)]\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall s \in V,\; \operatorname{activeStemFamily}\left(G, s\right) = \{S \in \operatorname{domSets}\left(G\right) | \neg \operatorname{stemBlock}\left(G, s\right) \subseteq S\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.activeStemFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retain the dominating sets that do not contain the whole stem block.

**Theorem 1.7 (Stem-block counting bound).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)]\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall s \in V,\; \operatorname{Nonempty}\left(\operatorname{leafNeighbors}\left(G, s\right)\right) \Rightarrow \sum_\{S \in \operatorname{activeStemFamily}\left(G, s\right)\} \operatorname{card}\left(\operatorname{inter}\left(\operatorname{criticalVertices}\left(G, S\right), \operatorname{stemBlock}\left(G, s\right)\right)\right) \le \sum_\{S \in \operatorname{activeStemFamily}\left(G, s\right)\} \operatorname{card}\left(\operatorname{sdiff}\left(\operatorname{stemBlock}\left(G, s\right), S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.activeStemFamily_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pair each dominating set omitting the stem with its replacement selecting the stem and no leaves. The original has k critical and one omitted block vertex; its replacement has one critical and k omitted block vertices. The injection cancels these contributions. Each remaining active set contains the stem and has one critical block vertex and at least one omitted leaf.

**Theorem 1.8 (Strictness for at least three leaves).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)]\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall s \in V,\; 3 \le \operatorname{leafCount}\left(G, s\right) \Rightarrow \sum_\{S \in \operatorname{activeStemFamily}\left(G, s\right)\} \operatorname{card}\left(\operatorname{inter}\left(\operatorname{criticalVertices}\left(G, S\right), \operatorname{stemBlock}\left(G, s\right)\right)\right) < \sum_\{S \in \operatorname{activeStemFamily}\left(G, s\right)\} \operatorname{card}\left(\operatorname{sdiff}\left(\operatorname{stemBlock}\left(G, s\right), S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.activeStemFamily_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Select every vertex except the stem, and substitute the stem together with one leaf. At least two leaves remain omitted and only the stem is critical in the block. This set cannot be an empty-leaf replacement, so its positive surplus remains after cancellation.

**Theorem 1.9 (Exact balance in star-like blocks).**

$$\forall V \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(V\right)][\operatorname{DecidableEq}\left(V\right)]\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall s \in V,\; \operatorname{StarLike}\left(G\right) \Rightarrow \left(\left(\operatorname{leafCount}\left(G, s\right) = 1 \lor \operatorname{leafCount}\left(G, s\right) = 2\right) \Rightarrow \sum_\{S \in \operatorname{activeStemFamily}\left(G, s\right)\} \operatorname{card}\left(\operatorname{inter}\left(\operatorname{criticalVertices}\left(G, S\right), \operatorname{stemBlock}\left(G, s\right)\right)\right) = \sum_\{S \in \operatorname{activeStemFamily}\left(G, s\right)\} \operatorname{card}\left(\operatorname{sdiff}\left(\operatorname{stemBlock}\left(G, s\right), S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.activeStemFamily_eq_of_starLike` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With one leaf every selected-stem active set has zero gap. With two leaves any selected-stem set omitting both leaves comes from an omitted-stem predecessor: replace the stem by its leaves. Every other neighbour is itself a stem and retains a leaf neighbour, so domination is preserved. The remaining sets have one omitted and one critical block vertex, giving equality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.activeStemFamily`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.activeStemFamily_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.activeStemFamily_eq_of_starLike`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.activeStemFamily_strict`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.stemBlock`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.stemBlocks`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.stemBlocks_pairwiseDisjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.stemSwap`
- Truth anchor: `D5/S3/Combinatorics/Graph/DominatingSetAverageBoundStem.stemSwap_dominating`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting](DominatingSetAverageBoundCounting.md)
