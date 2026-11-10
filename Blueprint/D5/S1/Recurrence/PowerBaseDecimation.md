# PowerBaseDecimation

## Abstract

PowerBaseDecimation

The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

An arbitrary commutative unital coefficient ring R is fixed. Intermediate binary decimations of levels below h give a finite indexed family from a literal base-2^h family, for every h at least one. Coefficients are fixed and no independence or invertibility is assumed. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Definition 1.1 (BaseFamily).**

Lean statement: `D5/S1/Recurrence/PowerBaseDecimation.BaseFamily`

*Formalization.* `D5/S1/Recurrence/PowerBaseDecimation.BaseFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: def BaseFamily (k : ℕ) (a : ℕ → R) : Prop := ∃ (ι : Type) (hι : Fintype ι), letI : Fintype ι := hι; ∃ (b : ι → ℕ → R) (i0 : ι) (c : Fin k → ι → ι → R), (∀ n, b i0 n = a n) ∧ (∀ (r : Fin k) i n, b i (k * n + r.val) = ∑ j, c r i j * b j n)

**Theorem 1.2 (powerBase_binary).**

Lean statement: `D5/S1/Recurrence/PowerBaseDecimation.powerBase_binary`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/PowerBaseDecimation.powerBase_binary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem powerBase_binary (h : ℕ) (hh : 1 ≤ h) (a : ℕ → R) (ha : BaseFamily (2 ^ h) a) : ArbitraryFamily a

## References

- Truth anchor: `D5/S1/Recurrence/PowerBaseDecimation.BaseFamily`
- Truth anchor: `D5/S1/Recurrence/PowerBaseDecimation.powerBase_binary`
- Dependency: [D5/S1/Recurrence/BinaryDecimation](BinaryDecimation.md)
