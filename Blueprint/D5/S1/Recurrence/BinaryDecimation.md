# BinaryDecimation

## Abstract

BinaryDecimation

The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

Fixed binary matrices and finite indexed families are over an arbitrary commutative unital ring R. Matrix recurrence theorems additionally assume 1 is not 0. The given matrix dimension d is exactly the monic forward recurrence order. All natural inputs are retained. There is no basis, independence, invertibility, characteristic-zero, domain or Noetherian assumption. Cayley-Hamilton and recurrence uniqueness come from pinned Mathlib. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Definition 1.1 (MatrixFamily).**

Lean statement: `D5/S1/Recurrence/BinaryDecimation.MatrixFamily`

*Formalization.* `D5/S1/Recurrence/BinaryDecimation.MatrixFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: def MatrixFamily (a : ℕ → R) : Prop := ∃ d : ℕ, ∃ hd : 0 < d, ∃ F : ℕ → Fin d → R, ∃ M0 M1 : Matrix (Fin d) (Fin d) R, (∀ n, F n ⟨0, hd⟩ = a n) ∧ (∀ n, F (2 * n) = M0.mulVec (F n)) ∧ (∀ n, F (2 * n + 1) = M1.mulVec (F n))

**Definition 1.2 (ClosedFamily).**

Lean statement: `D5/S1/Recurrence/BinaryDecimation.ClosedFamily`

*Formalization.* `D5/S1/Recurrence/BinaryDecimation.ClosedFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: def ClosedFamily (a : ℕ → R) : Prop := ∃ d : ℕ, ∃ hd : 0 < d, ∃ b : Fin d → ℕ → R, ∃ c0 c1 : Fin d → Fin d → R, (∀ n, b ⟨0, hd⟩ n = a n) ∧ (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧ (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)

**Definition 1.3 (ArbitraryFamily).**

Lean statement: `D5/S1/Recurrence/BinaryDecimation.ArbitraryFamily`

*Formalization.* `D5/S1/Recurrence/BinaryDecimation.ArbitraryFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: def ArbitraryFamily (a : ℕ → R) : Prop := ∃ (ι : Type) (hι : Fintype ι), letI : Fintype ι := hι; ∃ (b : ι → ℕ → R) (i0 : ι) (c0 c1 : ι → ι → R), (∀ n, b i0 n = a n) ∧ (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧ (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)

**Theorem 1.4 (closed_matrix_iff).**

Lean statement: `D5/S1/Recurrence/BinaryDecimation.closed_matrix_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BinaryDecimation.closed_matrix_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem closed_matrix_iff (a : ℕ → R) : ClosedFamily a ↔ MatrixFamily a

**Theorem 1.5 (arbitrary_matrix_iff).**

Lean statement: `D5/S1/Recurrence/BinaryDecimation.arbitrary_matrix_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BinaryDecimation.arbitrary_matrix_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem arbitrary_matrix_iff (a : ℕ → R) : ArbitraryFamily a ↔ MatrixFamily a

**Theorem 1.6 (dyadic_fixed_matrix_recurrence).**

Lean statement: `D5/S1/Recurrence/BinaryDecimation.dyadic_fixed_matrix_recurrence`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BinaryDecimation.dyadic_fixed_matrix_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem dyadic_fixed_matrix_recurrence [Nontrivial R] (a : ℕ → R) (d : ℕ) (hd : 0 < d) (F : ℕ → Fin d → R) (M0 M1 : Matrix (Fin d) (Fin d) R) (hf : ∀ n, F n ⟨0, hd⟩ = a n) (he : ∀ n, F (2 * n) = M0.mulVec (F n)) (ho : ∀ n, F (2 * n + 1) = M1.mulVec (F n)) : ∃ E : LinearRecurrence R, E.order = d ∧ E.IsSolution (fun n => a (2 ^ (n + 2) + 1))

**Theorem 1.7 (dyadic_matrix_recurrence).**

Lean statement: `D5/S1/Recurrence/BinaryDecimation.dyadic_matrix_recurrence`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BinaryDecimation.dyadic_matrix_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem dyadic_matrix_recurrence [Nontrivial R] (a : ℕ → R) (ha : MatrixFamily a) : ∃ E : LinearRecurrence R, 0 < E.order ∧ E.IsSolution (fun n => a (2 ^ (n + 2) + 1))

**Theorem 1.8 (shifted_sub_solution).**

Lean statement: `D5/S1/Recurrence/BinaryDecimation.shifted_sub_solution`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/BinaryDecimation.shifted_sub_solution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem shifted_sub_solution (E : LinearRecurrence R) (u : ℕ → R) (hu : E.IsSolution u) (t : R) : E.IsSolution (fun n => u (n + 1) - t * u n)

## References

- Truth anchor: `D5/S1/Recurrence/BinaryDecimation.ArbitraryFamily`
- Truth anchor: `D5/S1/Recurrence/BinaryDecimation.ClosedFamily`
- Truth anchor: `D5/S1/Recurrence/BinaryDecimation.MatrixFamily`
- Truth anchor: `D5/S1/Recurrence/BinaryDecimation.arbitrary_matrix_iff`
- Truth anchor: `D5/S1/Recurrence/BinaryDecimation.closed_matrix_iff`
- Truth anchor: `D5/S1/Recurrence/BinaryDecimation.dyadic_fixed_matrix_recurrence`
- Truth anchor: `D5/S1/Recurrence/BinaryDecimation.dyadic_matrix_recurrence`
- Truth anchor: `D5/S1/Recurrence/BinaryDecimation.shifted_sub_solution`
