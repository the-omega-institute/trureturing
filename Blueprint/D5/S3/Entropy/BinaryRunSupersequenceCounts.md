# BinaryRunSupersequenceCounts

## Abstract

Exact binary run counts and input entropy for two deletions and insertions.

**Definition 1.1 (wordSum).**

$$\forall (n: \mathbb{N}), (\forall (F: (\operatorname{List} \operatorname{Bool}) \to (\mathbb{R})), (\operatorname{wordSum} n F = (\sum_{x : \operatorname{Fin} n \to \operatorname{Bool}} (F (\operatorname{List}.\operatorname{ofFn} x)))))$$

*Formalization.* `D5/S3/Entropy/BinaryRunSupersequenceCounts.wordSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines wordSum.

**Definition 1.2 (leadingWeight).**

$$\begin{aligned}\operatorname{leadingWeight} [] = (0)\\\forall (r: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{leadingWeight} (r :: rs) = (\operatorname{if} r = 1 \operatorname{then} 1 + \operatorname{leadingWeight} rs \operatorname{else} r)))\end{aligned}$$

*Formalization.* `D5/S3/Entropy/BinaryRunSupersequenceCounts.leadingWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines leadingWeight.

**Theorem 1.3 (wordSum_succ).**

$$\forall (n: \mathbb{N}), (\forall (b: \operatorname{Bool}), (\forall (F: (\operatorname{List} \operatorname{Bool}) \to (\mathbb{R})), (\operatorname{wordSum} (n + 1) F = \operatorname{wordSum} n (\operatorname{fun} w\mapsto (F (b :: w))) + \operatorname{wordSum} n (\operatorname{fun} w\mapsto (F ((! b) :: w))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/BinaryRunSupersequenceCounts.wordSum_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.4 (wordSum_congr).**

$$\forall (n: \mathbb{N}), (\forall (F: (\operatorname{List} \operatorname{Bool}) \to (\mathbb{R})), (\forall (G: (\operatorname{List} \operatorname{Bool}) \to (\mathbb{R})), ((\forall x, ((x.\operatorname{length} = n) \to (F x = G x))) \to (\operatorname{wordSum} n F = \operatorname{wordSum} n G))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/BinaryRunSupersequenceCounts.wordSum_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.5 (wordSum_add).**

$$\forall (n: \mathbb{N}), (\forall (F: (\operatorname{List} \operatorname{Bool}) \to (\mathbb{R})), (\forall (G: (\operatorname{List} \operatorname{Bool}) \to (\mathbb{R})), (\operatorname{wordSum} n (\operatorname{fun} x\mapsto (F x + G x)) = \operatorname{wordSum} n F + \operatorname{wordSum} n G)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/BinaryRunSupersequenceCounts.wordSum_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.6 (oneWordSum).**

$$\forall (w: \operatorname{List} \operatorname{Bool}), (\forall (G: (\mathbb{N}) \to (\mathbb{R})), (\operatorname{oneWordSum} w G = (\operatorname{wordSum} (w.\operatorname{length} + 1) (\operatorname{fun} x\mapsto (G (\operatorname{scatteredCount} w x))))))$$

*Formalization.* `D5/S3/Entropy/BinaryRunSupersequenceCounts.oneWordSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines oneWordSum.

**Definition 1.7 (jointWordSum).**

$$\forall (w: \operatorname{List} \operatorname{Bool}), (\forall (F: (\mathbb{N}) \to ((\mathbb{N}) \to (\mathbb{R}))), (\operatorname{jointWordSum} w F = (\operatorname{wordSum} (w.\operatorname{length} + 1) (\operatorname{fun} x\mapsto (F (\operatorname{scatteredCount} w x) (\operatorname{scatteredCount} w.\operatorname{tail} x))))))$$

*Formalization.* `D5/S3/Entropy/BinaryRunSupersequenceCounts.jointWordSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines jointWordSum.

**Theorem 1.8 (oneWordSum_runs).**

$$\forall (b: \operatorname{Bool}), (\forall (rs: \operatorname{List} \mathbb{N}), ((\forall r \in rs, (0 < r)) \to (\forall (G: (\mathbb{N}) \to (\mathbb{R})), ((G 0 = 0) \to (\operatorname{oneWordSum} (\operatorname{runWord} b rs) G = (rs.\operatorname{map} (\operatorname{fun} r\mapsto (G (r + 1)))) . \operatorname{sum} + ((rs.\operatorname{sum}: \mathbb{R}) + 2 - rs.\operatorname{length}) \cdot G 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/BinaryRunSupersequenceCounts.oneWordSum_runs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.9 (jointWordSum_runs).**

$$\forall (b: \operatorname{Bool}), (\forall (rs: \operatorname{List} \mathbb{N}), ((\forall r \in rs, (0 < r)) \to (\forall (r: \mathbb{N}), (\forall (F: (\mathbb{N}) \to ((\mathbb{N}) \to (\mathbb{R}))), ((\forall d, (F 0 d = 0)) \to (\operatorname{jointWordSum} (\operatorname{runWord} b ((r + 1) :: rs)) F = F (r + 2) ((r + 2) . \operatorname{choose} 2) + (rs.\operatorname{map} (\operatorname{fun} t\mapsto (F (t + 1) ((r + 1) \cdot (t + 1))))) . \operatorname{sum} + ((r: \mathbb{R}) + 1 + rs.\operatorname{sum} - rs.\operatorname{length}) \cdot F 1 (r + 1) + F 1 (r + 1 + \operatorname{leadingWeight} rs)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/BinaryRunSupersequenceCounts.jointWordSum_runs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The joint one-supersequence count distribution is determined by the first run length, the later run lengths, and the leading singleton chain. The function F is arbitrary subject to F 0 d = 0.

## References

- Truth anchor: `D5/S3/Entropy/BinaryRunSupersequenceCounts.jointWordSum`
- Truth anchor: `D5/S3/Entropy/BinaryRunSupersequenceCounts.jointWordSum_runs`
- Truth anchor: `D5/S3/Entropy/BinaryRunSupersequenceCounts.leadingWeight`
- Truth anchor: `D5/S3/Entropy/BinaryRunSupersequenceCounts.oneWordSum`
- Truth anchor: `D5/S3/Entropy/BinaryRunSupersequenceCounts.oneWordSum_runs`
- Truth anchor: `D5/S3/Entropy/BinaryRunSupersequenceCounts.wordSum`
- Truth anchor: `D5/S3/Entropy/BinaryRunSupersequenceCounts.wordSum_add`
- Truth anchor: `D5/S3/Entropy/BinaryRunSupersequenceCounts.wordSum_congr`
- Truth anchor: `D5/S3/Entropy/BinaryRunSupersequenceCounts.wordSum_succ`
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](../../S1/Words/Complexity/VivionBinomialConverseFails.md)
- Dependency: [D5/S1/Words/TwoDeletionRunDecks](../../S1/Words/TwoDeletionRunDecks.md)
- Dependency: [D5/S3/Entropy/AlternatingTwoDeletionCounts](AlternatingTwoDeletionCounts.md)
