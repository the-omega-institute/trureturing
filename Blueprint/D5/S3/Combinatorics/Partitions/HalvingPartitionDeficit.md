# HalvingPartitionDeficit

## Abstract

HalvingPartitionDeficit

The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

The Stern sequence is the existing published AdamsonSternFareyInverse.stern, with recursion facts exposed at their original place. The deficit is actual Stern minus actual halving count, using natural subtraction. All m≥2 and every even dilation are retained; floor-log bounds and an ordinary real-log O(1) estimate are separate verified statements. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Definition 1.1 (deficit).**

Lean statement: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit`

*Formalization.* `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def deficit (n : ℕ) : ℕ := stern n - count n

**Theorem 1.2 (stern_dyadic_successor).**

Lean statement: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.stern_dyadic_successor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.stern_dyadic_successor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem stern_dyadic_successor (m : ℕ) : stern (2 ^ m + 1) = m + 1

**Theorem 1.3 (deficit_dyadic).**

Lean statement: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_dyadic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_dyadic` (`✓ std3`). ∎

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

Exact source declaration: theorem deficit_dyadic (m : ℕ) (hm : 2 ≤ m) : deficit (2 ^ m + 1) = m - 2 - thresholdCount m

**Theorem 1.4 (deficit_dyadic_dilation).**

Lean statement: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_dyadic_dilation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_dyadic_dilation` (`✓ std3`). ∎

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

Exact source declaration: theorem deficit_dyadic_dilation (m v : ℕ) (hm : 2 ≤ m) : deficit (2 ^ v * (2 ^ m + 1)) = m - 2 - thresholdCount m

**Theorem 1.5 (deficit_log_bounds).**

Lean statement: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_log_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem deficit_log_bounds (m : ℕ) (hm : 4 ≤ m) : m - Nat.log2 m - 2 ≤ deficit (2 ^ m + 1) ∧ deficit (2 ^ m + 1) ≤ m - Nat.log2 m - 1

**Theorem 1.6 (deficit_real_log_bound).**

Lean statement: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_real_log_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_real_log_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem deficit_real_log_bound (m : ℕ) (hm : 4 ≤ m) : |(deficit (2 ^ m + 1) : ℝ) - ((m : ℝ) - Real.logb 2 m)| ≤ 4

**Theorem 1.7 (deficit_log_isBigO).**

Lean statement: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_log_isBigO`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_log_isBigO` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem deficit_log_isBigO : Asymptotics.IsBigO Filter.atTop (fun m : ℕ => (deficit (2 ^ m + 1) : ℝ) - ((m : ℝ) - Real.logb 2 m)) (fun _ : ℕ => (1 : ℝ))

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_dyadic`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_dyadic_dilation`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_log_bounds`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_log_isBigO`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.deficit_real_log_bound`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HalvingPartitionDeficit.stern_dyadic_successor`
- Dependency: [D5/S1/Recurrence/Partitions/HalvingPartitionDilation](../../../S1/Recurrence/Partitions/HalvingPartitionDilation.md)
- Dependency: [D5/S1/Recurrence/Partitions/HalvingPartitionGrowth](../../../S1/Recurrence/Partitions/HalvingPartitionGrowth.md)
- Dependency: [D5/S3/PrimeForms/SternBrocot/AdamsonSternFareyInverse](../../PrimeForms/SternBrocot/AdamsonSternFareyInverse.md)
