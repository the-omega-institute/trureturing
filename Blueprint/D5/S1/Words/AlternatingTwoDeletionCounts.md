# AlternatingTwoDeletionCounts

## Abstract

Exact binary run counts and input entropy for two deletions and insertions.

**Theorem 1.1 (sum_binary_real_succ).**

$$\forall (n: \mathbb{N}), (\forall (F: (((\operatorname{Fin} (n + 1)) \to (\operatorname{Bool}))) \to (\mathbb{R})), (\forall (b: \operatorname{Bool}), ((\sum_{x} (F x)) = (\sum_{x : \operatorname{Fin} n \to \operatorname{Bool}} (F (\operatorname{Fin}.\operatorname{cons} b x))) + \sum_{x : \operatorname{Fin} n \to \operatorname{Bool}} (F (\operatorname{Fin}.\operatorname{cons} (! b) x)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.sum_binary_real_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.2 (altList).**

$$\forall (b: \operatorname{Bool}), (\forall (n: \mathbb{N}), (\operatorname{altList} b n = (\operatorname{List}.\operatorname{ofFn} (\operatorname{fun} i : \operatorname{Fin} n\mapsto (\operatorname{D5}.\operatorname{S3}.\operatorname{Observer}.\operatorname{ProbabilisticClosure}.\operatorname{AdaptiveMarkerStoppingTails}.\operatorname{alternatingBit} b i.\operatorname{val})))))$$

*Formalization.* `D5/S1/Words/AlternatingTwoDeletionCounts.altList` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines altList.

**Theorem 1.3 (altList_zero).**

$$\forall (b: \operatorname{Bool}), (\operatorname{altList} b 0 = [])$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.altList_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.4 (altList_succ).**

$$\forall (b: \operatorname{Bool}), (\forall (n: \mathbb{N}), (\operatorname{altList} b (n + 1) = b :: \operatorname{altList} (! b) n))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.altList_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.5 (count_equal_length).**

$$\forall (p: \operatorname{List} \operatorname{Bool}), (\forall (q: \operatorname{List} \operatorname{Bool}), ((p.\operatorname{length} = q.\operatorname{length}) \to (\operatorname{scatteredCount} p q = \operatorname{if} p = q \operatorname{then} 1 \operatorname{else} 0)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.count_equal_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.6 (count_alt_cons_same).**

$$\forall (b: \operatorname{Bool}), (\forall (m: \mathbb{N}), (\forall (q: \operatorname{List} \operatorname{Bool}), (\operatorname{scatteredCount} (\operatorname{altList} b (m + 1)) (b :: q) = \operatorname{scatteredCount} (\operatorname{altList} b (m + 1)) q + \operatorname{scatteredCount} (\operatorname{altList} (! b) m) q)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.count_alt_cons_same` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.7 (count_alt_cons_opposite).**

$$\forall (b: \operatorname{Bool}), (\forall (m: \mathbb{N}), (\forall (q: \operatorname{List} \operatorname{Bool}), (\operatorname{scatteredCount} (\operatorname{altList} b (m + 1)) ((! b) :: q) = \operatorname{scatteredCount} (\operatorname{altList} b (m + 1)) q)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.count_alt_cons_opposite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.8 (altList_not).**

$$\forall (b: \operatorname{Bool}), (\forall (n: \mathbb{N}), (\operatorname{altList} (! b) n = (\operatorname{altList} b n) . \operatorname{map} \operatorname{Bool}.\operatorname{not}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.altList_not` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.9 (ofFn_alternating).**

$$\forall (n: \mathbb{N}), (\operatorname{List}.\operatorname{ofFn} ((\operatorname{fun} i : \operatorname{Fin} n\mapsto (\operatorname{decide} (i.\operatorname{val} \bmod 2 = 1)))) = \operatorname{altList} \operatorname{false} n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.ofFn_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.10 (count_alt_two).**

$$\forall (n: \mathbb{N}), (\forall (b: \operatorname{Bool}), ((\operatorname{scatteredCount} (\operatorname{altList} b n) (\operatorname{altList} b (n + 2)) = n + 1) \land (\forall p : \operatorname{List} \operatorname{Bool}, ((p.\operatorname{length} = n) \to ((p \neq \operatorname{altList} b n) \to (\operatorname{scatteredCount} p (\operatorname{altList} b (n + 2)) \leq 1))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.count_alt_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.11 (sum_one_extra_alt).**

$$\forall (m: \mathbb{N}), (\forall (b: \operatorname{Bool}), (\forall (F: (\mathbb{N}) \to (\mathbb{R})), ((F 0 = 0) \to ((\sum_{y : \operatorname{Fin} (m + 1) \to \operatorname{Bool}} (F (\operatorname{scatteredCount} (\operatorname{altList} b m) (\operatorname{List}.\operatorname{ofFn} y)))) = 2 \cdot F 1 + (m: \mathbb{R}) \cdot F 2))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.sum_one_extra_alt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.12 (sum_one_two_joint).**

$$\forall (m: \mathbb{N}), ((1 \leq m) \to (\forall (b: \operatorname{Bool}), (\forall (F: (\mathbb{N}) \to ((\mathbb{N}) \to (\mathbb{R}))), ((\forall d, (F 0 d = 0)) \to ((\sum_{y : \operatorname{Fin} (m + 2) \to \operatorname{Bool}} (F (\operatorname{scatteredCount} (\operatorname{altList} b (m + 1)) (\operatorname{List}.\operatorname{ofFn} y)) (\operatorname{scatteredCount} (\operatorname{altList} (! b) m) (\operatorname{List}.\operatorname{ofFn} y)))) = F 1 (m + 1) + F 1 1 + F 2 1 + (m: \mathbb{R}) \cdot F 2 2)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AlternatingTwoDeletionCounts.sum_one_two_joint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

## References

- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.altList`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.altList_not`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.altList_succ`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.altList_zero`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.count_alt_cons_opposite`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.count_alt_cons_same`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.count_alt_two`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.count_equal_length`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.ofFn_alternating`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.sum_binary_real_succ`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.sum_one_extra_alt`
- Truth anchor: `D5/S1/Words/AlternatingTwoDeletionCounts.sum_one_two_joint`
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore](Complexity/ExactDecks/Growth/ExactDeckCore.md)
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](Complexity/VivionBinomialConverseFails.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails](../../S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.md)
