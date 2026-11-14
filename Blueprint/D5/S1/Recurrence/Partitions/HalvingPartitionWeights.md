# HalvingPartitionWeights

## Abstract

HalvingPartitionWeights

The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

Weights and lengths are read from the same actual positive ordered lists, with virtual predecessor n, repeated terminal ones and the unique empty list at zero. Integer step digits are p_(i-1)-2*p_i+1; the exponent counts literal digit ones. The complete dyadic polynomial uses truncated natural exponents, so m=2 yields W_t(5)=2+t. The parameter t is arbitrary, including zero and nonunits. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Definition 1.1 (evenSteps).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.evenSteps`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.evenSteps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: def evenSteps : ℕ → List ℕ → ℕ | _, [] => 0 | previous, next :: rest => (if previous = 2 * next then 1 else 0) + evenSteps next rest

**Theorem 1.2 (digit_one_iff).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.digit_one_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.digit_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem digit_one_iff (previous next : ℕ) : (previous : ℤ) - 2 * next + 1 = 1 ↔ previous = 2 * next

**Definition 1.3 (stepDigits).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.stepDigits`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.stepDigits` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: def stepDigits : ℕ → List ℕ → List ℤ | _, [] => [] | previous, next :: rest => ((previous : ℤ) - 2 * next + 1) :: stepDigits next rest

**Theorem 1.4 (evenSteps_eq_count).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.evenSteps_eq_count`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.evenSteps_eq_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem evenSteps_eq_count (previous : ℕ) (parts : List ℕ) : evenSteps previous parts = (stepDigits previous parts).count 1

**Definition 1.5 (weightedCount).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def weightedCount {R : Type*} [CommSemiring R] (t : R) (n : ℕ) : R := ∑ p : SourceLists n, t ^ (stepDigits n p.val).count 1

**Definition 1.6 (weightedLengthPolynomial).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedLengthPolynomial`

*Formalization.* `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedLengthPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: noncomputable def weightedLengthPolynomial {R : Type*} [CommSemiring R] (t : R) (n : ℕ) : Polynomial R := ∑ p : SourceLists n, Polynomial.C (t ^ (stepDigits n p.val).count 1) * Polynomial.X ^ p.val.length

**Theorem 1.7 (codeSource_steps).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.codeSource_steps`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.codeSource_steps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem codeSource_steps (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) : evenSteps (2 ^ m + 1) (codeSource m hm c).val = match c with | .inl i => if i = 0 then m - 3 else if i = 1 then m - 2 else m - 1 | .inr r => m - r.val.val - 2 ^ r.val.val - 2

**Theorem 1.8 (weightedLengthPolynomial_dyadic).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedLengthPolynomial_dyadic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedLengthPolynomial_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weightedLengthPolynomial_dyadic {R : Type*} [CommRing R] (t : R) (m : ℕ) (hm : 2 ≤ m) : weightedLengthPolynomial t (2 ^ m + 1) = Polynomial.X ^ m * Polynomial.C (t ^ (m - 3)) + Polynomial.X ^ (m + 1) * Polynomial.C (t ^ (m - 2)) + Polynomial.X ^ (m + 2) * Polynomial.C (t ^ (m - 1)) + ∑ r : Threshold m, Polynomial.X ^ (m - r.val.val) * Polynomial.C (t ^ (m - r.val.val - 2 ^ r.val.val - 2))

**Theorem 1.9 (weightedCount_dyadic).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount_dyadic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount_dyadic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weightedCount_dyadic {R : Type*} [CommRing R] (t : R) (m : ℕ) (hm : 2 ≤ m) : weightedCount t (2 ^ m + 1) = t ^ (m - 3) + t ^ (m - 2) + t ^ (m - 1) + ∑ r : Threshold m, t ^ (m - r.val.val - 2 ^ r.val.val - 2)

**Theorem 1.10 (weightedCount_zero).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount_zero`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weightedCount_zero {R : Type*} [CommRing R] (t : R) : weightedCount t 0 = 1

**Theorem 1.11 (weightedCount_one).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount_one`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weightedCount_one {R : Type*} [CommRing R] (n : ℕ) : weightedCount (1 : R) n = (count n : R)

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.codeSource_steps`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.digit_one_iff`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.evenSteps`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.evenSteps_eq_count`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.stepDigits`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount_dyadic`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount_one`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedCount_zero`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedLengthPolynomial`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionWeights.weightedLengthPolynomial_dyadic`
- Dependency: [D5/S1/Recurrence/Partitions/HalvingPartitionProfile](HalvingPartitionProfile.md)
