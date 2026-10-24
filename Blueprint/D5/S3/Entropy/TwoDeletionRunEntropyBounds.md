# TwoDeletionRunEntropyBounds

## Abstract

Exact binary run counts and input entropy for two deletions and insertions.

**Definition 1.1 (f).**

$$\forall (x: \mathbb{R}), (f x = (x \cdot \operatorname{Real}.\operatorname{logb} 2 x))$$

*Formalization.* `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f` (`✓ std3`).

*Citation.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The weighted embedding term is t times its base-two logarithm; its value at zero is zero.

**Definition 1.2 (longRuns).**

$$\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{longRuns} rs = (rs.\operatorname{filter} (\operatorname{fun} r\mapsto (2 \leq r))))$$

*Formalization.* `D5/S3/Entropy/TwoDeletionRunEntropyBounds.longRuns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines longRuns.

**Definition 1.3 (bridgeWeightsAux).**

$$\begin{aligned}\forall (prev: \mathbb{N}), (\forall (singles: \mathbb{N}), (\operatorname{bridgeWeightsAux} prev singles [] = ([prev + singles + 1])))\\\forall (prev: \mathbb{N}), (\forall (singles: \mathbb{N}), (\forall (r: \mathbb{N}), (\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{bridgeWeightsAux} prev singles (r :: rs) = (\operatorname{if} r = 1 \operatorname{then} \operatorname{bridgeWeightsAux} prev (singles + 1) rs \operatorname{else} (prev + r + singles + 1) :: \operatorname{bridgeWeightsAux} r 0 rs)))))\end{aligned}$$

*Formalization.* `D5/S3/Entropy/TwoDeletionRunEntropyBounds.bridgeWeightsAux` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines bridgeWeightsAux.

**Definition 1.4 (runDefect).**

$$\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{runDefect} rs = ((rs.\operatorname{map} (\operatorname{fun} r\mapsto (r - 1))) . \operatorname{sum}))$$

*Formalization.* `D5/S3/Entropy/TwoDeletionRunEntropyBounds.runDefect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines runDefect.

**Theorem 1.5 (f_zero).**

$$f 0 = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.6 (f_one).**

$$f 1 = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.7 (f_two).**

$$f 2 = 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.8 (f_mul).**

$$\forall (a: \mathbb{R}), (\forall (b: \mathbb{R}), (f (a \cdot b) = b \cdot f a + a \cdot f b))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.9 (Hrun).**

$$\forall (m: \mathbb{R}), (\forall (r: \mathbb{R}), (\operatorname{Hrun} m r = (f ((r + 1) \cdot (r + 2) / 2) + (2 \cdot m - r) \cdot f (r + 1))))$$

*Formalization.* `D5/S3/Entropy/TwoDeletionRunEntropyBounds.Hrun` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines Hrun.

**Theorem 1.10 (longRuns_bounds).**

$$\forall (rs: \operatorname{List} \mathbb{N}), ((\forall r \in rs, (0 < r)) \to (((\forall r \in \operatorname{longRuns} rs, ((2 \leq r) \land (r \leq rs.\operatorname{sum})))) \land ((\operatorname{longRuns} rs) . \operatorname{sum} \leq rs.\operatorname{sum})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.longRuns_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.11 (longRuns_nonempty_of_defect).**

$$\forall (rs: \operatorname{List} \mathbb{N}), ((\forall r \in rs, (0 < r)) \to ((0 < \operatorname{runDefect} rs) \to (\operatorname{longRuns} rs \neq [])))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.longRuns_nonempty_of_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.12 (runDefect_eq).**

$$\forall (rs: \operatorname{List} \mathbb{N}), ((\forall r \in rs, (0 < r)) \to (\operatorname{runDefect} rs + rs.\operatorname{length} = rs.\operatorname{sum}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.runDefect_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.13 (runPhiInsertion).**

$$\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{runPhiInsertion} rs = (((\operatorname{collisionWeights} rs) . \operatorname{map} (\operatorname{fun} n : \mathbb{N}\mapsto (f n))) . \operatorname{sum}))$$

*Formalization.* `D5/S3/Entropy/TwoDeletionRunEntropyBounds.runPhiInsertion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines runPhiInsertion.

**Theorem 1.14 (same_run_phi_formula).**

$$\forall (rs: \operatorname{List} \mathbb{N}), (((\operatorname{sameRunWeights} rs) . \operatorname{map} (\operatorname{fun} n : \mathbb{N}\mapsto (f n))) . \operatorname{sum} = (rs.\operatorname{map} (\operatorname{fun} r\mapsto (f (r.\operatorname{choose} 2)))) . \operatorname{sum})$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.same_run_phi_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.15 (bridgeWeights_constraints).**

$$\forall (rs: \operatorname{List} \mathbb{N}), ((\forall r \in rs, (0 < r)) \to (((\operatorname{bridgeWeightsAux} 0 0 rs) . \operatorname{length} = (\operatorname{longRuns} rs) . \operatorname{length} + 1) \land ((\operatorname{bridgeWeightsAux} 0 0 rs) . \operatorname{sum} = rs.\operatorname{sum} + (\operatorname{longRuns} rs) . \operatorname{sum} + (\operatorname{longRuns} rs) . \operatorname{length} + 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.bridgeWeights_constraints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Definition 1.16 (deletionRunScore).**

$$\forall (rs: \operatorname{List} \mathbb{N}), (\operatorname{deletionRunScore} rs = (((rs.\operatorname{sum} - (\operatorname{longRuns} rs) . \operatorname{sum}: \mathbb{N}): \mathbb{R}) \cdot (f 3 + 4 \cdot rs.\operatorname{sum}) + ((\operatorname{longRuns} rs) . \operatorname{map} (\operatorname{fun} r : \mathbb{N}\mapsto (\operatorname{Hrun} (rs.\operatorname{sum}: \mathbb{R}) (r: \mathbb{R})))) . \operatorname{sum} + ((\operatorname{bridgeWeightsAux} 0 0 rs) . \operatorname{map} (\operatorname{fun} r : \mathbb{N}\mapsto (f r))) . \operatorname{sum}))$$

*Formalization.* `D5/S3/Entropy/TwoDeletionRunEntropyBounds.deletionRunScore` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed expression defines deletionRunScore.

**Theorem 1.17 (large_insertion_comparison).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (P: \mathbb{R}), ((9 \leq n) \to ((1 \leq d) \to ((2 \cdot ((n: \mathbb{R}) - 2) \cdot d \leq P) \to (((2 \cdot d < n - 5) \to (f (n - 1: \mathbb{N}) + (d: \mathbb{R}) \cdot ((n: \mathbb{R}) - 2 \cdot d - 5) \leq P)) \to (f (n - 1: \mathbb{N}) < P)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.large_insertion_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.18 (f_add_super_nat).**

$$\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (f a + f b \leq f ((a + b: \mathbb{N}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f_add_super_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.19 (run_fine_insertion_bound).**

$$\forall (rs: \operatorname{List} \mathbb{N}), ((\forall r \in rs, (0 < r)) \to ((3 \leq rs.\operatorname{length}) \to (f (rs.\operatorname{sum} - 1: \mathbb{N}) + (\operatorname{runDefect} rs: \mathbb{R}) \cdot ((rs.\operatorname{sum}: \mathbb{R}) - 2 \cdot \operatorname{runDefect} rs - 5) \leq \operatorname{runPhiInsertion} rs)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.run_fine_insertion_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

**Theorem 1.20 (deletion_abstract_bridge_gap).**

$$\forall (m: \mathbb{N}), (\forall (us: \operatorname{List} \mathbb{N}), (\forall (ws: \operatorname{List} \mathbb{N}), ((2 \leq m) \to ((us \neq []) \to ((\forall u \in us, ((2 \leq u) \land (u \leq m))) \to ((us.\operatorname{sum} \leq m) \to ((ws.\operatorname{length} = us.\operatorname{length} + 1) \to ((m + us.\operatorname{sum} + us.\operatorname{length} + 1 \leq ws.\operatorname{sum}) \to (4 \cdot (m: \mathbb{R})^{2} + 3 \cdot m \cdot \operatorname{Real}.\operatorname{logb} 2 3 + f ((m: \mathbb{R}) + 1) < ((m - us.\operatorname{sum}: \mathbb{N}): \mathbb{R}) \cdot (f 3 + 4 \cdot m) + (us.\operatorname{map} (\operatorname{fun} u : \mathbb{N}\mapsto (\operatorname{Hrun} (m: \mathbb{R}) (u: \mathbb{R})))) . \operatorname{sum} + (ws.\operatorname{map} (\operatorname{fun} n : \mathbb{N}\mapsto (f n))) . \operatorname{sum})))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.deletion_abstract_bridge_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

A nonempty family of long runs and the associated bridge constraints force a strict increase above the alternating deletion score.

**Theorem 1.21 (run_coarse_insertion_bound).**

$$\forall (rs: \operatorname{List} \mathbb{N}), ((\forall r \in rs, (0 < r)) \to (2 \cdot ((rs.\operatorname{sum}: \mathbb{R}) - 2) \cdot ((rs.\operatorname{sum}: \mathbb{R}) - rs.\operatorname{length}) \leq \operatorname{runPhiInsertion} rs))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/TwoDeletionRunEntropyBounds.run_coarse_insertion_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* S. Singhvi; O. Sabary; D. Bar-Lev; E. Yaakobi (2025). *Conditional Entropies of k-Deletion/Insertion Channels*. DOI: [10.1109/TIT.2025.3581849](https://doi.org/10.1109/TIT.2025.3581849). URL: <https://arxiv.org/abs/2407.10026v2>.

*Commentary.*

The displayed identity or comparison relates binary embedding counts and their run profiles.

## References

- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.Hrun`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.bridgeWeightsAux`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.bridgeWeights_constraints`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.deletionRunScore`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.deletion_abstract_bridge_gap`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f_add_super_nat`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f_mul`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f_one`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f_two`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.f_zero`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.large_insertion_comparison`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.longRuns`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.longRuns_bounds`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.longRuns_nonempty_of_defect`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.runDefect`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.runDefect_eq`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.runPhiInsertion`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.run_coarse_insertion_bound`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.run_fine_insertion_bound`
- Truth anchor: `D5/S3/Entropy/TwoDeletionRunEntropyBounds.same_run_phi_formula`
- Dependency: [D5/S1/Words/TwoDeletionRunDecks](../../S1/Words/TwoDeletionRunDecks.md)
