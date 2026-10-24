# TwoDeletionRunDecks

## Abstract

Exact binary run counts and input entropy for two deletions and insertions.

**Definition 1.1 (adjacentWeights).**

$$\begin{aligned}\operatorname{adjacentWeights} [] = ([])\\\forall (a: \mathbb{N}), (\operatorname{adjacentWeights} [a] = ([]))\\\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{adjacentWeights} (a :: b :: rs) = (a \cdot b :: \operatorname{adjacentWeights} (b :: rs)))))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.adjacentWeights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines adjacentWeights.

**Definition 1.2 (pairWeights).**

$$\begin{aligned}\operatorname{pairWeights} [] = ([])\\\forall (a: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{pairWeights} (a :: rs) = (rs.\operatorname{map} (\operatorname{fun} b\mapsto (a \cdot b)) ++ \operatorname{pairWeights} rs)))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.pairWeights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines pairWeights.

**Definition 1.3 (prefixBlocks).**

$$\forall (pre: \operatorname{List} \operatorname{Bool}), (\forall (bs: \operatorname{List} (\operatorname{List} \operatorname{Bool} \times \mathbb{N})), (\operatorname{prefixBlocks} pre bs = (bs.\operatorname{map} (\operatorname{fun} p\mapsto ((pre ++ p.1 , p.2))))))$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.prefixBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines prefixBlocks.

**Definition 1.4 (deletionDeck).**

$$\forall (\alpha: \operatorname{Type}), (\forall (k: \mathbb{N}), (\forall (w: \operatorname{List} \alpha), (\operatorname{deletionDeck} (\alpha := \alpha) k w = (\operatorname{if} k \leq w.\operatorname{length} \operatorname{then} w.\operatorname{sublistsLen} (w.\operatorname{length} - k) \operatorname{else} []))))$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.deletionDeck` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines deletionDeck.

**Definition 1.5 (runWord).**

$$\begin{aligned}\forall (b: \operatorname{Bool}), (\operatorname{runWord} b [] = ([]))\\\forall (b: \operatorname{Bool}), (\forall (r: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{runWord} b (r :: rs) = (\operatorname{List}.\operatorname{replicate} r b ++ \operatorname{runWord} (! b) rs))))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.runWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines runWord.

**Definition 1.6 (sameRunWeights).**

$$\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{sameRunWeights} rs = ((rs.\operatorname{filter} \operatorname{fun} r\mapsto (2 \leq r)) . \operatorname{map} (\operatorname{fun} r\mapsto (r.\operatorname{choose} 2))))$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.sameRunWeights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines sameRunWeights.

**Definition 1.7 (nonadjacentWeights).**

$$\begin{aligned}\operatorname{nonadjacentWeights} [] = ([])\\\forall (a: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{nonadjacentWeights} (a :: rs) = ((rs.\operatorname{drop} 1) . \operatorname{map} (\operatorname{fun} b\mapsto (a \cdot b)) ++ \operatorname{nonadjacentWeights} rs)))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.nonadjacentWeights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines nonadjacentWeights.

**Definition 1.8 (componentWeightsAux).**

$$\begin{aligned}\forall (acc: \mathbb{N}), (\forall (prev: \mathbb{N}), (\operatorname{componentWeightsAux} acc prev [] = ([acc])))\\\forall (acc: \mathbb{N}), (\forall (prev: \mathbb{N}), (\forall (r: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{componentWeightsAux} acc prev (r :: rs) = (\operatorname{if} prev = 1 \operatorname{then} \operatorname{componentWeightsAux} (acc + prev \cdot r) r rs \operatorname{else} acc :: \operatorname{componentWeightsAux} (prev \cdot r) r rs)))))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.componentWeightsAux` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines componentWeightsAux.

**Theorem 1.9 (blockLengths_positive).**

$$\forall (w: \operatorname{List} \operatorname{Bool}), (\forall r \in \operatorname{blockLengths} w, (0 < r))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TwoDeletionRunDecks.blockLengths_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.10 (realizeBlocks).**

$$\forall (\alpha: \operatorname{Type}), (\forall (bs: \operatorname{List} (\alpha \times \mathbb{N})), (\operatorname{realizeBlocks} (\alpha := \alpha) bs = (bs.\operatorname{flatMap} (\operatorname{fun} p\mapsto (\operatorname{List}.\operatorname{replicate} p.2 p.1)))))$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.realizeBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines realizeBlocks.

**Definition 1.11 (mergeWeightedAux).**

$$\begin{aligned}\forall (\alpha: \operatorname{Type}), (\forall (p: \alpha \times \mathbb{N}), (\forall (prev: \mathbb{N}), (\forall (\operatorname{es}: \operatorname{List} (\alpha \times \mathbb{N})), (\operatorname{mergeWeightedAux} (\alpha := \alpha) p prev [] \operatorname{es} = ([p])))))\\\forall (\alpha: \operatorname{Type}), (\forall (p: \alpha \times \mathbb{N}), (\forall (prev: \mathbb{N}), (\forall (r: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{mergeWeightedAux} (\alpha := \alpha) p prev (r :: rs) [] = ([p]))))))\\\forall (\alpha: \operatorname{Type}), (\forall (p: \alpha \times \mathbb{N}), (\forall (q: \alpha \times \mathbb{N}), (\forall (prev: \mathbb{N}), (\forall (r: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\forall (\operatorname{qs}: \operatorname{List} (\alpha \times \mathbb{N})), (\operatorname{mergeWeightedAux} (\alpha := \alpha) p prev (r :: rs) (q :: \operatorname{qs}) = (\operatorname{if} prev = 1 \operatorname{then} \operatorname{mergeWeightedAux} (p.1 , p.2 + q.2) r rs \operatorname{qs} \operatorname{else} p :: \operatorname{mergeWeightedAux} q r rs \operatorname{qs}))))))))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.mergeWeightedAux` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines mergeWeightedAux.

**Definition 1.12 (oneRunBlocks).**

$$\begin{aligned}\forall (b: \operatorname{Bool}), (\operatorname{oneRunBlocks} b [] = ([]))\\\forall (b: \operatorname{Bool}), (\forall (r: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{oneRunBlocks} b (r :: rs) = ((\operatorname{List}.\operatorname{replicate} (r - 1) b ++ \operatorname{runWord} (! b) rs , r) :: ((\operatorname{oneRunBlocks} (! b) rs) . \operatorname{map} (\operatorname{fun} p\mapsto ((\operatorname{List}.\operatorname{replicate} r b ++ p.1 , p.2))))))))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.oneRunBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines oneRunBlocks.

**Definition 1.13 (edgeLabel).**

$$\forall (b: \operatorname{Bool}), (\forall (a: \mathbb{N}), (\forall (c: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{edgeLabel} b a c rs = (\operatorname{List}.\operatorname{replicate} (a - 1) b ++ \operatorname{List}.\operatorname{replicate} (c - 1) (! b) ++ \operatorname{runWord} b rs)))))$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.edgeLabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines edgeLabel.

**Definition 1.14 (sameBlocks).**

$$\begin{aligned}\forall (b: \operatorname{Bool}), (\operatorname{sameBlocks} b [] = ([]))\\\forall (b: \operatorname{Bool}), (\forall (a: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{sameBlocks} b (a :: rs) = ((\operatorname{List}.\operatorname{replicate} (a - 2) b ++ \operatorname{runWord} (! b) rs , a.\operatorname{choose} 2) :: \operatorname{prefixBlocks} (\operatorname{List}.\operatorname{replicate} a b) (\operatorname{sameBlocks} (! b) rs)))))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.sameBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines sameBlocks.

**Definition 1.15 (componentWeights).**

$$\begin{aligned}\operatorname{componentWeights} [] = ([])\\\forall (a: \mathbb{N}), (\operatorname{componentWeights} [a] = ([]))\\\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{componentWeights} (a :: b :: rs) = (\operatorname{componentWeightsAux} (a \cdot b) b rs))))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.componentWeights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines componentWeights.

**Theorem 1.16 (runWord_length).**

$$\forall (b: \operatorname{Bool}), (\forall (rs: \operatorname{List} \mathbb{N}), ((\operatorname{runWord} b rs) . \operatorname{length} = rs.\operatorname{sum}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TwoDeletionRunDecks.runWord_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.17 (adjacentBlocks).**

$$\begin{aligned}\forall (b: \operatorname{Bool}), (\operatorname{adjacentBlocks} b [] = ([]))\\\forall (b: \operatorname{Bool}), (\forall (a: \mathbb{N}), (\operatorname{adjacentBlocks} b [a] = ([])))\\\forall (b: \operatorname{Bool}), (\forall (a: \mathbb{N}), (\forall (c: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{adjacentBlocks} b (a :: c :: rs) = ((\operatorname{edgeLabel} b a c rs , a \cdot c) :: \operatorname{prefixBlocks} (\operatorname{List}.\operatorname{replicate} a b) (\operatorname{adjacentBlocks} (! b) (c :: rs)))))))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.adjacentBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines adjacentBlocks.

**Definition 1.18 (nonadjBlocks).**

$$\begin{aligned}\forall (b: \operatorname{Bool}), (\operatorname{nonadjBlocks} b [] = ([]))\\\forall (b: \operatorname{Bool}), (\forall (a: \mathbb{N}), (\operatorname{nonadjBlocks} b [a] = ([])))\\\forall (b: \operatorname{Bool}), (\forall (a: \mathbb{N}), (\forall (c: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{nonadjBlocks} b (a :: c :: rs) = (((\operatorname{oneRunBlocks} b rs) . \operatorname{map} (\operatorname{fun} p\mapsto ((\operatorname{List}.\operatorname{replicate} (a - 1) b ++ \operatorname{List}.\operatorname{replicate} c (! b) ++ p.1 , a \cdot p.2)))) ++ \operatorname{prefixBlocks} (\operatorname{List}.\operatorname{replicate} a b) (\operatorname{nonadjBlocks} (! b) (c :: rs)))))))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.nonadjBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines nonadjBlocks.

**Theorem 1.19 (sameBlocks_weights).**

$$\forall (b: \operatorname{Bool}), (\forall (rs: \operatorname{List} \mathbb{N}), ((\operatorname{sameBlocks} b rs) . \operatorname{map} \operatorname{Prod}.\operatorname{snd} = rs.\operatorname{map} (\operatorname{fun} a\mapsto (a.\operatorname{choose} 2))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TwoDeletionRunDecks.sameBlocks_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.20 (collisionWeights).**

$$\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{collisionWeights} rs = (\operatorname{sameRunWeights} rs ++ \operatorname{nonadjacentWeights} rs ++ \operatorname{componentWeights} rs))$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.collisionWeights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines collisionWeights.

**Theorem 1.21 (runWord_blockLengths).**

$$\forall (w: \operatorname{List} \operatorname{Bool}), (\operatorname{runWord} (w.\operatorname{headD} \operatorname{false}) (\operatorname{blockLengths} w) = w)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TwoDeletionRunDecks.runWord_blockLengths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.22 (componentBlocks).**

$$\begin{aligned}\forall (b: \operatorname{Bool}), (\operatorname{componentBlocks} b [] = ([]))\\\forall (b: \operatorname{Bool}), (\forall (a: \mathbb{N}), (\operatorname{componentBlocks} b [a] = ([])))\\\forall (b: \operatorname{Bool}), (\forall (a: \mathbb{N}), (\forall (c: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{componentBlocks} b (a :: c :: rs) = (\operatorname{mergeWeightedAux} (\operatorname{edgeLabel} b a c rs , a \cdot c) c rs (\operatorname{prefixBlocks} (\operatorname{List}.\operatorname{replicate} a b) (\operatorname{adjacentBlocks} (! b) (c :: rs))))))))\end{aligned}$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.componentBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines componentBlocks.

**Theorem 1.23 (nonadjBlocks_weights).**

$$\forall (b: \operatorname{Bool}), (\forall (rs: \operatorname{List} \mathbb{N}), ((\operatorname{nonadjBlocks} b rs) . \operatorname{map} \operatorname{Prod}.\operatorname{snd} = \operatorname{nonadjacentWeights} rs))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TwoDeletionRunDecks.nonadjBlocks_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.24 (twoDeletionDeck_eq_deletionDeck).**

$$\forall (w: \operatorname{List} \operatorname{Bool}), ((2 \leq w.\operatorname{length}) \to ((w.\operatorname{sublistsLen} (w.\operatorname{length} - 2)) = \operatorname{deletionDeck} 2 w))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TwoDeletionRunDecks.twoDeletionDeck_eq_deletionDeck` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.25 (componentBlocks_weights).**

$$\forall (b: \operatorname{Bool}), (\forall (rs: \operatorname{List} \mathbb{N}), ((\operatorname{componentBlocks} b rs) . \operatorname{map} \operatorname{Prod}.\operatorname{snd} = \operatorname{componentWeights} rs))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TwoDeletionRunDecks.componentBlocks_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.26 (collisionBlocks).**

$$\forall (b: \operatorname{Bool}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{collisionBlocks} b rs = (\operatorname{sameBlocks} b rs ++ \operatorname{nonadjBlocks} b rs ++ \operatorname{componentBlocks} b rs)))$$

*Formalization.* `D5/S1/Words/TwoDeletionRunDecks.collisionBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines collisionBlocks.

**Theorem 1.27 (collisionBlocks_realize).**

$$\forall (b: \operatorname{Bool}), (\forall (rs: \operatorname{List} \mathbb{N}), ((\forall r \in rs, (0 < r)) \to ((\operatorname{realizeBlocks} (\operatorname{collisionBlocks} b rs)) . \operatorname{Perm} (\operatorname{deletionDeck} 2 (\operatorname{runWord} b rs)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/TwoDeletionRunDecks.collisionBlocks_realize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

## References

- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.adjacentBlocks`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.adjacentWeights`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.blockLengths_positive`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.collisionBlocks`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.collisionBlocks_realize`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.collisionWeights`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.componentBlocks`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.componentBlocks_weights`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.componentWeights`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.componentWeightsAux`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.deletionDeck`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.edgeLabel`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.mergeWeightedAux`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.nonadjBlocks`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.nonadjBlocks_weights`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.nonadjacentWeights`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.oneRunBlocks`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.pairWeights`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.prefixBlocks`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.realizeBlocks`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.runWord`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.runWord_blockLengths`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.runWord_length`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.sameBlocks`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.sameBlocks_weights`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.sameRunWeights`
- Truth anchor: `D5/S1/Words/TwoDeletionRunDecks.twoDeletionDeck_eq_deletionDeck`
- Dependency: [D5/S1/Words/AssociatedMersenne/RunTupleBijection](AssociatedMersenne/RunTupleBijection.md)
