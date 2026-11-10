# HalvingPartitionGrowth

## Abstract

HalvingPartitionGrowth

The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

R_m counts every positive threshold 2^r+r+1≤m. For m≥4, floor(log_2 m)+2≤a(2^m+1)≤floor(log_2 m)+3. The ordinary real logarithm is Real.logb 2; the bounded absolute error yields the standard atTop O(1) assertion. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Theorem 1.1 (thresholdCount_log_bounds).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.thresholdCount_log_bounds`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.thresholdCount_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem thresholdCount_log_bounds (m : ℕ) (hm : 4 ≤ m) : Nat.log2 m - 1 ≤ thresholdCount m ∧ thresholdCount m ≤ Nat.log2 m

**Theorem 1.2 (dyadic_count_log_bounds).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.dyadic_count_log_bounds`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.dyadic_count_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem dyadic_count_log_bounds (m : ℕ) (hm : 4 ≤ m) : Nat.log2 m + 2 ≤ count (2 ^ m + 1) ∧ count (2 ^ m + 1) ≤ Nat.log2 m + 3

**Theorem 1.3 (dyadic_count_real_log_bound).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.dyadic_count_real_log_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.dyadic_count_real_log_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem dyadic_count_real_log_bound (m : ℕ) (hm : 4 ≤ m) : |(count (2 ^ m + 1) : ℝ) - Real.logb 2 m| ≤ 3

**Theorem 1.4 (dyadic_count_log_isBigO).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.dyadic_count_log_isBigO`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.dyadic_count_log_isBigO` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem dyadic_count_log_isBigO : Asymptotics.IsBigO Filter.atTop (fun m : ℕ => (count (2 ^ m + 1) : ℝ) - Real.logb 2 m) (fun _ : ℕ => (1 : ℝ))

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.dyadic_count_log_bounds`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.dyadic_count_log_isBigO`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.dyadic_count_real_log_bound`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionGrowth.thresholdCount_log_bounds`
- Dependency: [D5/S1/Recurrence/Partitions/HalvingPartitionProfile](HalvingPartitionProfile.md)
