# HalvingPartitionStatistics

## Abstract

HalvingPartitionStatistics

The full mean and variance audits are declared_validated. The residue-balance audit remains missing its complete mirrored four-slot realization and current source binding. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

The mean and central second moment are rational uniform averages over the actual SourceLists carrier. The finite length interval has one list per integer, giving mean m+1-R_m/2 and variance ((R_m+3)^2-1)/12 for every m≥2. Residue balance holds for every positive modulus and every two residue classes, by an actual injection with at most one overflow. The square-sum is reused directly from Mathlib Faulhaber. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Definition 1.1 (meanLength).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.meanLength`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.meanLength` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def meanLength (n : ℕ) : ℚ := (∑ p : SourceLists n, (p.val.length : ℚ)) / count n

**Definition 1.2 (varianceLength).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.varianceLength`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.varianceLength` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def varianceLength (n : ℕ) : ℚ := (∑ p : SourceLists n, ((p.val.length : ℚ) - meanLength n) ^ 2) / count n

**Theorem 1.3 (meanLength_dyadic).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.meanLength_dyadic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.meanLength_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem meanLength_dyadic (m : ℕ) (hm : 2 ≤ m) : meanLength (2 ^ m + 1) = m + 1 - (thresholdCount m : ℚ) / 2

**Theorem 1.4 (varianceLength_dyadic).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.varianceLength_dyadic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.varianceLength_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem varianceLength_dyadic (m : ℕ) (hm : 2 ≤ m) : varianceLength (2 ^ m + 1) = (((thresholdCount m : ℚ) + 3) ^ 2 - 1) / 12

**Definition 1.5 (lengthResidueCount).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.lengthResidueCount`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.lengthResidueCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def lengthResidueCount (n b r : ℕ) : ℕ := Nat.card {p : SourceLists n // p.val.length % b = r}

**Theorem 1.6 (lengthResidueCount_balanced).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.lengthResidueCount_balanced`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.lengthResidueCount_balanced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem lengthResidueCount_balanced (m b : ℕ) (hm : 2 ≤ m) (hb : 0 < b) (r s : Fin b) : lengthResidueCount (2 ^ m + 1) b r.val ≤ lengthResidueCount (2 ^ m + 1) b s.val + 1

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.lengthResidueCount`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.lengthResidueCount_balanced`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.meanLength`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.meanLength_dyadic`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.varianceLength`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.varianceLength_dyadic`
- Dependency: [D5/S1/Recurrence/Partitions/HalvingPartitionProfile](HalvingPartitionProfile.md)
