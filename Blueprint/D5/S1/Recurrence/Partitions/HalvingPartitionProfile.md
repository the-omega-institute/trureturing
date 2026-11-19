# HalvingPartitionProfile

## Abstract

HalvingPartitionProfile

The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

Exact source-length fibers use the original exhaustive list/code bijection at its original declaration. All m≥2 and all natural lengths are included. The support is exactly the integer interval from m-R_m to m+2, with one actual list per length. Total parts uses natural subtraction and exact natural division, rather than an informal rational rearrangement. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Definition 1.1 (sourceFintype).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.sourceFintype`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.sourceFintype` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable instance sourceFintype (n : ℕ) : Fintype (SourceLists n) := Fintype.ofFinite _

**Definition 1.2 (lengthCount).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthCount`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def lengthCount (n ell : ℕ) : ℕ := Nat.card {p : SourceLists n // p.val.length = ell}

**Definition 1.3 (lengthPolynomial).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthPolynomial`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def lengthPolynomial (n : ℕ) : Polynomial ℕ := ∑ p : SourceLists n, Polynomial.X ^ p.val.length

**Theorem 1.4 (codeSource_length).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.codeSource_length`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.codeSource_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem codeSource_length (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) : (codeSource m hm c).val.length = (codeParams m c).1

**Theorem 1.5 (source_length_injective).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.source_length_injective`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.source_length_injective` (`✓ std3`). ∎

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

Exact source declaration: theorem source_length_injective (m : ℕ) : Function.Injective (fun p : SourceLists (2 ^ m + 1) => p.val.length)

**Theorem 1.6 (source_length_support).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.source_length_support`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.source_length_support` (`✓ std3`). ∎

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

Exact source declaration: theorem source_length_support (m ell : ℕ) (hm : 2 ≤ m) : (∃ p : SourceLists (2 ^ m + 1), p.val.length = ell) ↔ ell = m ∨ ell = m + 1 ∨ ell = m + 2 ∨ ∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m ∧ ell = m - r

**Theorem 1.7 (lengthCount_dyadic).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthCount_dyadic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthCount_dyadic` (`✓ std3`). ∎

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

Exact source declaration: theorem lengthCount_dyadic (m ell : ℕ) (hm : 2 ≤ m) : lengthCount (2 ^ m + 1) ell = if ell = m ∨ ell = m + 1 ∨ ell = m + 2 ∨ (∃ r : ℕ, 1 ≤ r ∧ 2 ^ r + r + 1 ≤ m ∧ ell = m - r) then 1 else 0

**Theorem 1.8 (sum_source_dyadic).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.sum_source_dyadic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.sum_source_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem sum_source_dyadic {A : Type*} [AddCommMonoid A] (m : ℕ) (hm : 2 ≤ m) (f : SourceLists (2 ^ m + 1) → A) : ∑ p, f p = ∑ c : DyadicCode m, f (codeSource m hm c)

**Theorem 1.9 (lengthPolynomial_dyadic).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthPolynomial_dyadic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthPolynomial_dyadic` (`✓ std3`). ∎

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

Exact source declaration: theorem lengthPolynomial_dyadic (m : ℕ) (hm : 2 ≤ m) : lengthPolynomial (2 ^ m + 1) = Polynomial.X ^ m * (1 + Polynomial.X + Polynomial.X ^ 2) + ∑ r : Threshold m, Polynomial.X ^ (m - r.val.val)

**Definition 1.10 (thresholdCount).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.thresholdCount`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.thresholdCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: def thresholdCount (m : ℕ) : ℕ := Fintype.card (Threshold m)

**Theorem 1.11 (threshold_iff_le_count).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.threshold_iff_le_count`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.threshold_iff_le_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem threshold_iff_le_count (m r : ℕ) : (1 ≤ r ∧ 2 ^ r + r + 1 ≤ m) ↔ (1 ≤ r ∧ r ≤ thresholdCount m)

**Theorem 1.12 (thresholdCount_lt).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.thresholdCount_lt`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.thresholdCount_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem thresholdCount_lt (m : ℕ) (hm : 2 ≤ m) : thresholdCount m < m

**Theorem 1.13 (source_length_interval).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.source_length_interval`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.source_length_interval` (`✓ std3`). ∎

*Citation.* Max A. Alekseyev (2026). *Halving Partitions and Hyperbinary Expansions*. URL: <https://arxiv.org/abs/2611.01243v1>.

*Commentary.*

Exact source declaration: theorem source_length_interval (m ell : ℕ) (hm : 2 ≤ m) : (∃ p : SourceLists (2 ^ m + 1), p.val.length = ell) ↔ m - thresholdCount m ≤ ell ∧ ell ≤ m + 2

**Definition 1.14 (lengthIntervalEquiv).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthIntervalEquiv`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthIntervalEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def lengthIntervalEquiv (m : ℕ) (hm : 2 ≤ m) : SourceLists (2 ^ m + 1) ≃ Fin (thresholdCount m + 3) := by let f : SourceLists (2 ^ m + 1) → Fin (thresholdCount m + 3) := fun p => ⟨p.val.length - (m - thresholdCount m), by have hp := (source_length_interval m p.val.length hm).mp ⟨p, rfl⟩ have hr := thresholdCount_lt m hm omega⟩ apply Equiv.ofBijective f constructor · intro p q h apply source_length_injective m change p.val.length = q.val.length have he := congrArg Fin.val h have hp := (source_length_interval m p.val.length hm).mp ⟨p, rfl⟩ have hq := (source_length_interval m q.val.length hm).mp ⟨q, rfl⟩ change p.val.length - (m - thresholdCount m) = q.val.length - (m - thresholdCount m) at he omega · intro i have hr := thresholdCount_lt m hm have hi := i.isLt obtain ⟨p, hp⟩ := (source_length_interval m (m - thresholdCount m + i.val) hm).mpr ⟨by omega, by omega⟩ refine ⟨p, Fin.ext ?_⟩ change p.val.length - (m - thresholdCount m) = i.val omega

**Theorem 1.15 (lengthIntervalEquiv_length).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthIntervalEquiv_length`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthIntervalEquiv_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem lengthIntervalEquiv_length (m : ℕ) (hm : 2 ≤ m) (p : SourceLists (2 ^ m + 1)) : p.val.length = m - thresholdCount m + (lengthIntervalEquiv m hm p).val

**Theorem 1.16 (sum_source_lengths).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.sum_source_lengths`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.sum_source_lengths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem sum_source_lengths {A : Type*} [AddCommMonoid A] (m : ℕ) (hm : 2 ≤ m) (f : ℕ → A) : ∑ p : SourceLists (2 ^ m + 1), f p.val.length = ∑ i : Fin (thresholdCount m + 3), f (m - thresholdCount m + i.val)

**Definition 1.17 (totalParts).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def totalParts (n : ℕ) : ℕ := ∑ p : SourceLists n, p.val.length

**Theorem 1.18 (totalParts_eq_derivative).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts_eq_derivative`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts_eq_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

For every n, totalParts n = (lengthPolynomial n).derivative.eval 1. The exact length polynomial is consumed through this derivative in the total-parts proof.

**Theorem 1.19 (totalParts_twice).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts_twice`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts_twice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem totalParts_twice (m : ℕ) (hm : 2 ≤ m) : 2 * totalParts (2 ^ m + 1) = (thresholdCount m + 3) * (2 * m + 2 - thresholdCount m)

**Theorem 1.20 (totalParts_dyadic).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts_dyadic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem totalParts_dyadic (m : ℕ) (hm : 2 ≤ m) : totalParts (2 ^ m + 1) = (thresholdCount m + 3) * m + 3 - thresholdCount m * (thresholdCount m + 1) / 2

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.codeSource_length`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthCount`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthCount_dyadic`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthIntervalEquiv`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthIntervalEquiv_length`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthPolynomial`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.lengthPolynomial_dyadic`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.sourceFintype`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.source_length_injective`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.source_length_interval`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.source_length_support`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.sum_source_dyadic`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.sum_source_lengths`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.thresholdCount`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.thresholdCount_lt`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.threshold_iff_le_count`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts_dyadic`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts_eq_derivative`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionProfile.totalParts_twice`
- Dependency: [D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity](HalvingPartitionNonregularity.md)
