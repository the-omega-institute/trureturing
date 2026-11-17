# HalvingPartitionWeightedNonregularity

## Abstract

HalvingPartitionWeightedNonregularity

The full binary and power-base weighted audits compile their realization, variation, sensitivity and dependence proofs, but current source binding is declared_unresolved with IE-C050 source.dictionary_or_proof_coordinate. The other new public audits in this owner remain missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

All weighted results hold for every nonzero commutative unital ring R, including positive characteristic and zero divisors, and every t in R. The weighted difference has impulses 1 and 1-t for m≥3. The separately proved unweighted difference includes m=2 and gives exactly 2^r consecutive zeros between jumps. The monic recurrence contradiction never divides by t or a recurrence coefficient. The representation base ranges over every 2^h with h≥1. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Definition 1.1 (weightedTail).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedTail`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedTail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: def weightedTail (t : R) (m r : ℕ) : R := if 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m then t ^ (m - r - 2 ^ r - 2) else 0

**Theorem 1.2 (weightedCount_bounded).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedCount_bounded`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedCount_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weightedCount_bounded (t : R) (m L : ℕ) (hm : 2 ≤ m) (hL : m < L) : weightedCount t (2 ^ m + 1) = t ^ (m - 3) + t ^ (m - 2) + t ^ (m - 1) + ∑ r ∈ Finset.range L, weightedTail t m r

**Definition 1.3 (weightedDifference).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def weightedDifference (t : R) (m : ℕ) : R := weightedCount t (2 ^ (m + 1) + 1) - t * weightedCount t (2 ^ m + 1)

**Theorem 1.4 (weightedDifference_impulses).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_impulses`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_impulses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weightedDifference_impulses (t : R) (m : ℕ) (hm : 3 ≤ m) : weightedDifference t m = ∑ r ∈ Finset.range (m + 2), if 1 ≤ r ∧ 2 ^ r + r = m then 1 else if 1 ≤ r ∧ 2 ^ r + r + 1 = m then 1 - t else 0

**Theorem 1.5 (weightedDifference_jump).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_jump`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_jump` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weightedDifference_jump (t : R) (r : ℕ) (hr : 1 ≤ r) : weightedDifference t (2 ^ r + r) = 1

**Theorem 1.6 (weightedDifference_after_jump).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_after_jump`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_after_jump` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weightedDifference_after_jump (t : R) (r : ℕ) (hr : 1 ≤ r) : weightedDifference t (2 ^ r + r + 1) = 1 - t

**Theorem 1.7 (weightedDifference_gap).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_gap`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weightedDifference_gap (t : R) (m r : ℕ) (hr : 1 ≤ r) (hlo : 2 ^ r + r + 1 < m) (hhi : m < 2 ^ (r + 1) + (r + 1)) : weightedDifference t m = 0

**Theorem 1.8 (count_difference).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.count_difference`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.count_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem count_difference (m : ℕ) (hm : 2 ≤ m) : (count (2 ^ (m + 1) + 1) : R) - (count (2 ^ m + 1) : R) = if ∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r = m then 1 else 0

**Theorem 1.9 (count_difference_zero_block).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.count_difference_zero_block`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.count_difference_zero_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem count_difference_zero_block (r i : ℕ) (hr : 1 ≤ r) (hi : i < 2 ^ r) : (count (2 ^ (2 ^ r + r + 1 + i + 1) + 1) : R) - (count (2 ^ (2 ^ r + r + 1 + i) + 1) : R) = 0

**Theorem 1.10 (weighted_nonregularity).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weighted_nonregularity`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weighted_nonregularity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weighted_nonregularity [Nontrivial R] (t : R) : ¬ BinaryDecimation.MatrixFamily (weightedCount t)

**Theorem 1.11 (weighted_powerBase_nonregularity).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weighted_powerBase_nonregularity`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weighted_powerBase_nonregularity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weighted_powerBase_nonregularity [Nontrivial R] (t : R) (h : ℕ) (hh : 1 ≤ h) : ¬ BinaryDecimation.BaseFamily (2 ^ h) (weightedCount t)

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.count_difference`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.count_difference_zero_block`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedCount_bounded`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_after_jump`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_gap`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_impulses`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedDifference_jump`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weightedTail`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weighted_nonregularity`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity.weighted_powerBase_nonregularity`
- Dependency: [D5/S1/Recurrence/Partitions/HalvingPartitionWeights](HalvingPartitionWeights.md)
- Dependency: [D5/S1/Recurrence/PowerBaseDecimation](../PowerBaseDecimation.md)
