# TwoDeletionChannelEntropy

## Abstract

Exact binary run counts and input entropy for two deletions and insertions.

**Theorem 1.1 (empty_embeddings).**

$$\forall (n: \mathbb{N}), (\forall (y: (\operatorname{Fin} n) \to (\operatorname{Bool})), (\operatorname{embeddings} (\operatorname{fun} i : \operatorname{Fin} 0\mapsto (\operatorname{Fin}.\operatorname{elim0} i)) y = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.empty_embeddings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.2 (phi).**

$$\forall (\iota: \operatorname{Type}), ([\operatorname{Fintype} \iota] \to (\forall (c: (\iota) \to (\mathbb{N})), (\operatorname{phi} (\iota := \iota) c = (\sum_{i} ((c i: \mathbb{R}) \cdot \operatorname{Real}.\operatorname{logb} 2 (c i))))))$$

*Formalization.* `D5/S3/Entropy/TwoDeletionChannelEntropy.phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines phi.

**Theorem 1.3 (ofFn_complement_alternating).**

$$\forall (n: \mathbb{N}), (\operatorname{List}.\operatorname{ofFn} (\operatorname{fun} i\mapsto (! (\operatorname{fun} i : \operatorname{Fin} n\mapsto (\operatorname{decide} (i.\operatorname{val} \bmod 2 = 1))) i)) = \operatorname{altList} \operatorname{true} n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.ofFn_complement_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.4 (RunDeletionCountingLowerBound).**

$$\operatorname{RunDeletionCountingLowerBound} = (\forall (m: \mathbb{N}) (y: (\operatorname{Fin} m) \to (\operatorname{Bool})) (b: \operatorname{Bool}) (rs: \operatorname{List} \mathbb{N}), (((\forall r \in rs, (0 < r))) \to ((\operatorname{List}.\operatorname{ofFn} y = \operatorname{runWord} b rs) \to (\operatorname{deletionRunScore} rs \leq \operatorname{phi} (\operatorname{fun} x : \operatorname{Fin} (m + 2) \to \operatorname{Bool}\mapsto (\operatorname{embeddings} y x))))))$$

*Formalization.* `D5/S3/Entropy/TwoDeletionChannelEntropy.RunDeletionCountingLowerBound` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines RunDeletionCountingLowerBound.

**Theorem 1.5 (alternating_insertion_phi).**

$$\forall (m: \mathbb{N}), (\operatorname{phi} (\operatorname{fun} x : \operatorname{Fin} m \to \operatorname{Bool}\mapsto (\operatorname{embeddings} x ((\operatorname{fun} i : \operatorname{Fin} (m + 2)\mapsto (\operatorname{decide} (i.\operatorname{val} \bmod 2 = 1)))))) = f (m + 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.alternating_insertion_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.6 (alternating_deletion_phi).**

$$\forall (m: \mathbb{N}), ((1 \leq m) \to (\operatorname{phi} (\operatorname{fun} x : \operatorname{Fin} (m + 2) \to \operatorname{Bool}\mapsto (\operatorname{embeddings} ((\operatorname{fun} i : \operatorname{Fin} m\mapsto (\operatorname{decide} (i.\operatorname{val} \bmod 2 = 1)))) x)) = 4 \cdot (m: \mathbb{R})^{2} + 3 \cdot m \cdot \operatorname{Real}.\operatorname{logb} 2 3 + ((m: \mathbb{R}) + 1) \cdot \operatorname{Real}.\operatorname{logb} 2 ((m: \mathbb{R}) + 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.alternating_deletion_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.7 (insertion_entropy_formula).**

$$\forall (m: \mathbb{N}), (\forall (y: (\operatorname{Fin} (m + 2)) \to (\operatorname{Bool})), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Entropy}.\operatorname{MaxEntropy}.\operatorname{shannonEntropy} ((\operatorname{fun} \{m: \mathbb{N}\} (y: (\operatorname{Fin} (m + 2)) \to (\operatorname{Bool})) (x: (\operatorname{Fin} m) \to (\operatorname{Bool}))\mapsto ((\operatorname{embeddings} x y: \mathbb{R}) / \sum_{x' : \operatorname{Fin} m \to \operatorname{Bool}} ((\operatorname{embeddings} x' y: \mathbb{R})))) y) / \operatorname{Real}.\operatorname{log} 2) = \operatorname{Real}.\operatorname{logb} 2 ((m + 2) . \operatorname{choose} m) - \operatorname{phi} (\operatorname{fun} x : \operatorname{Fin} m \to \operatorname{Bool}\mapsto (\operatorname{embeddings} x y)) / (m + 2) . \operatorname{choose} m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.insertion_entropy_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

For m ≥ 2, this is Lemma 3 with n = m and k = 2. The cases m = 0 and m = 1 extend the identity to the two shorter input lengths.

**Theorem 1.8 (alternating_insertion_closed_form).**

$$\forall (m: \mathbb{N}), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Entropy}.\operatorname{MaxEntropy}.\operatorname{shannonEntropy} ((\operatorname{fun} \{m: \mathbb{N}\} (y: (\operatorname{Fin} (m + 2)) \to (\operatorname{Bool})) (x: (\operatorname{Fin} m) \to (\operatorname{Bool}))\mapsto ((\operatorname{embeddings} x y: \mathbb{R}) / \sum_{x' : \operatorname{Fin} m \to \operatorname{Bool}} ((\operatorname{embeddings} x' y: \mathbb{R})))) ((\operatorname{fun} i : \operatorname{Fin} (m + 2)\mapsto (\operatorname{decide} (i.\operatorname{val} \bmod 2 = 1))))) / \operatorname{Real}.\operatorname{log} 2) = \operatorname{Real}.\operatorname{logb} 2 ((m + 2) . \operatorname{choose} 2) - ((m: \mathbb{R}) + 1) \cdot \operatorname{Real}.\operatorname{logb} 2 ((m: \mathbb{R}) + 1) / (m + 2) . \operatorname{choose} 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.alternating_insertion_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.9 (actual_run_insertion_lower).**

$$\forall (m: \mathbb{N}), (\forall (y: (\operatorname{Fin} (m + 2)) \to (\operatorname{Bool})), (\forall (b: \operatorname{Bool}), (\forall (rs: \operatorname{List} \mathbb{N}), ((\forall r \in rs, (0 < r)) \to ((\operatorname{List}.\operatorname{ofFn} y = \operatorname{runWord} b rs) \to (\operatorname{runPhiInsertion} rs \leq \operatorname{phi} (\operatorname{fun} x : \operatorname{Fin} m \to \operatorname{Bool}\mapsto (\operatorname{embeddings} x y))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.actual_run_insertion_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.10 (deletion_entropy_formula).**

$$\forall (m: \mathbb{N}), (\forall (y: (\operatorname{Fin} m) \to (\operatorname{Bool})), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Entropy}.\operatorname{MaxEntropy}.\operatorname{shannonEntropy} ((\operatorname{fun} \{m: \mathbb{N}\} (y: (\operatorname{Fin} m) \to (\operatorname{Bool})) (x: (\operatorname{Fin} (m + 2)) \to (\operatorname{Bool}))\mapsto ((\operatorname{embeddings} y x: \mathbb{R}) / \sum_{x' : \operatorname{Fin} (m + 2) \to \operatorname{Bool}} ((\operatorname{embeddings} y x': \mathbb{R})))) y) / \operatorname{Real}.\operatorname{log} 2) = \operatorname{Real}.\operatorname{logb} 2 (4 \cdot (m + 2) . \operatorname{choose} 2) - \operatorname{phi} (\operatorname{fun} x : \operatorname{Fin} (m + 2) \to \operatorname{Bool}\mapsto (\operatorname{embeddings} y x)) / (4 \cdot (m + 2) . \operatorname{choose} 2)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.deletion_entropy_formula` (`✓ std3`). ∎

*Citation.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.11 (insertion_entropy_product_formula).**

$$\forall (m: \mathbb{N}), (\forall (y: (\operatorname{Fin} (m + 2)) \to (\operatorname{Bool})), ((\operatorname{D5}.\operatorname{S3}.\operatorname{Entropy}.\operatorname{MaxEntropy}.\operatorname{shannonEntropy} ((\operatorname{fun} \{m: \mathbb{N}\} (y: (\operatorname{Fin} (m + 2)) \to (\operatorname{Bool})) (x: (\operatorname{Fin} m) \to (\operatorname{Bool}))\mapsto ((\operatorname{embeddings} x y: \mathbb{R}) / \sum_{x' : \operatorname{Fin} m \to \operatorname{Bool}} ((\operatorname{embeddings} x' y: \mathbb{R})))) y) / \operatorname{Real}.\operatorname{log} 2) = \operatorname{Real}.\operatorname{logb} 2 ((m + 2) . \operatorname{choose} m) - \operatorname{Real}.\operatorname{logb} 2 ((\prod_{i} ((((\operatorname{fun} x : \operatorname{Fin} m \to \operatorname{Bool}\mapsto (\operatorname{embeddings} x y))) i)^{(((\operatorname{fun} x : \operatorname{Fin} m \to \operatorname{Bool}\mapsto (\operatorname{embeddings} x y))) i)} : \mathbb{N}))) / (m + 2) . \operatorname{choose} m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.insertion_entropy_product_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.12 (alternating_deletion_closed_form).**

$$\forall (m: \mathbb{N}), ((1 \leq m) \to ((\operatorname{D5}.\operatorname{S3}.\operatorname{Entropy}.\operatorname{MaxEntropy}.\operatorname{shannonEntropy} ((\operatorname{fun} \{m: \mathbb{N}\} (y: (\operatorname{Fin} m) \to (\operatorname{Bool})) (x: (\operatorname{Fin} (m + 2)) \to (\operatorname{Bool}))\mapsto ((\operatorname{embeddings} y x: \mathbb{R}) / \sum_{x' : \operatorname{Fin} (m + 2) \to \operatorname{Bool}} ((\operatorname{embeddings} y x': \mathbb{R})))) ((\operatorname{fun} i : \operatorname{Fin} m\mapsto (\operatorname{decide} (i.\operatorname{val} \bmod 2 = 1))))) / \operatorname{Real}.\operatorname{log} 2) = \operatorname{Real}.\operatorname{logb} 2 (4 \cdot (m + 2) . \operatorname{choose} 2) - (4 \cdot (m: \mathbb{R})^{2} + 3 \cdot m \cdot \operatorname{Real}.\operatorname{logb} 2 3 + ((m: \mathbb{R}) + 1) \cdot \operatorname{Real}.\operatorname{logb} 2 ((m: \mathbb{R}) + 1)) / (4 \cdot (m + 2) . \operatorname{choose} 2)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.alternating_deletion_closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.13 (actual_run_deletion_lower).**

$$\forall (m: \mathbb{N}) (y: (\operatorname{Fin} m) \to (\operatorname{Bool})) (b: \operatorname{Bool}) (rs: \operatorname{List} \mathbb{N}), (((\forall r \in rs, (0 < r))) \to ((\operatorname{List}.\operatorname{ofFn} y = \operatorname{runWord} b rs) \to (\operatorname{deletionRunScore} rs \leq \operatorname{phi} (\operatorname{fun} x : \operatorname{Fin} (m + 2) \to \operatorname{Bool}\mapsto (\operatorname{embeddings} y x)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionChannelEntropy.actual_run_deletion_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

Every positive run profile of a received word gives a lower bound on its actual weighted embedding sum.

## References

- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.RunDeletionCountingLowerBound`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.actual_run_deletion_lower`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.actual_run_insertion_lower`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.alternating_deletion_closed_form`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.alternating_deletion_phi`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.alternating_insertion_closed_form`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.alternating_insertion_phi`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.deletion_entropy_formula`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.empty_embeddings`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.insertion_entropy_formula`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.insertion_entropy_product_formula`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.ofFn_complement_alternating`
- Truth anchor: `D5/S3/Entropy/TwoDeletionChannelEntropy.phi`
- Dependency: [D5/S0/Certificates/Hypergraphs/OrientationEntropyBalance](../../S0/Certificates/Hypergraphs/OrientationEntropyBalance.md)
- Dependency: [D5/S1/Words/AlternatingTwoDeletionCounts](../../S1/Words/AlternatingTwoDeletionCounts.md)
- Dependency: [D5/S1/Words/BinaryRunSupersequenceCounts](../../S1/Words/BinaryRunSupersequenceCounts.md)
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore](../../S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore.md)
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](../../S1/Words/Complexity/VivionBinomialConverseFails.md)
- Dependency: [D5/S1/Words/TwoDeletionRunDecks](../../S1/Words/TwoDeletionRunDecks.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts](../Arith/FibonacciAtomic/Observer/CommonPredictionWordCounts.md)
- Dependency: [D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation](../Combinatorics/Graph/DomiRankEntropyRefutation.md)
- Dependency: [D5/S3/Entropy/DeletionChannelEntropyOrdering](DeletionChannelEntropyOrdering.md)
- Dependency: [D5/S3/Entropy/MaxEntropy](MaxEntropy.md)
- Dependency: [D5/S3/Entropy/TwoDeletionRunEntropyBounds](TwoDeletionRunEntropyBounds.md)
