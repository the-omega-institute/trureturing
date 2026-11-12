# KernelDecimation

## Abstract

KernelDecimation

The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

The adopted arithmetic k-kernel consists of the actual subsequences n ↦ a(k^e*n+r) for every e and 0≤r<k^e. A finite kernel yields a literal finite indexed decimation family by one-hot coefficients over an arbitrary commutative unital ring. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Theorem 1.1 (finite_kernel_baseFamily).**

Lean statement: `D5/S1/Recurrence/KernelDecimation.finite_kernel_baseFamily`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/KernelDecimation.finite_kernel_baseFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem finite_kernel_baseFamily {R : Type*} [CommRing R] (k : ℕ) (a : ℕ → R) (hfin : Finite ↥(kKernel k a)) : BaseFamily k a

## References

- Truth anchor: `D5/S1/Recurrence/KernelDecimation.finite_kernel_baseFamily`
- Dependency: [D5/S0/Automata/FiniteKernelDFAO](../../S0/Automata/FiniteKernelDFAO.md)
- Dependency: [D5/S1/Recurrence/PowerBaseDecimation](PowerBaseDecimation.md)
