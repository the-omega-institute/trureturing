# CanonicalDFAOKernel

## Abstract

CanonicalDFAOKernel

The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

Finite canonical MSDF output machines have finite arithmetic kernels. Correctness is assumed only for positive canonical expansions; the proof treats the zero input separately and imposes no padding or zero-output convention. The adopted all-word LSDF equivalence is a different, explicitly named supplier. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Definition 1.1 (CanonicalAutomatic).**

Lean statement: `D5/S0/Automata/CanonicalDFAOKernel.CanonicalAutomatic`

*Formalization.* `D5/S0/Automata/CanonicalDFAOKernel.CanonicalAutomatic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: def CanonicalAutomatic {B : Type*} (k : ℕ) (hk : 2 ≤ k) (a : ℕ → B) : Prop := ∃ Q : Type, ∃ _ : Fintype Q, ∃ M : DFAO (Fin k) B Q, ∀ n, 0 < n → M.evalOutput (msfDigits k (by omega) n) = a n

**Theorem 1.2 (canonical_finite_kernel).**

Lean statement: `D5/S0/Automata/CanonicalDFAOKernel.canonical_finite_kernel`

*Proof.* Machine-checked in Lean as `D5/S0/Automata/CanonicalDFAOKernel.canonical_finite_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem canonical_finite_kernel {B : Type*} (k : ℕ) (hk : 2 ≤ k) (a : ℕ → B) (ha : CanonicalAutomatic k hk a) : Finite ↥(kKernel k a)

## References

- Truth anchor: `D5/S0/Automata/CanonicalDFAOKernel.CanonicalAutomatic`
- Truth anchor: `D5/S0/Automata/CanonicalDFAOKernel.canonical_finite_kernel`
- Dependency: [D5/S0/Automata/FiniteKernelDFAO](FiniteKernelDFAO.md)
- Dependency: [D5/S1/Recurrence/AntiRecurrenceAutomaticity](../../S1/Recurrence/AntiRecurrenceAutomaticity.md)
