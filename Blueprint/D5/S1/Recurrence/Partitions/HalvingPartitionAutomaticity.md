# HalvingPartitionAutomaticity

## Abstract

HalvingPartitionAutomaticity

The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.

Actual weighted SourceLists counts are excluded from finite canonical MSDF machines, even with unconstrained zero output, in every base 2^h with h≥1. Finite nonzero rings also use the adopted genuine all-word LSDF machine equivalence. The ordinary remainder a(n)%q is connected to its actual ZMod q cast for every q≥2, including composite moduli. No canonical/padding claim is inferred merely by renaming the finite-kernel predicate. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.

**Theorem 1.1 (weighted_not_canonical_automatic).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.weighted_not_canonical_automatic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.weighted_not_canonical_automatic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weighted_not_canonical_automatic {R : Type*} [CommRing R] [Nontrivial R] (t : R) (h : ℕ) (hh : 1 ≤ h) : ¬ CanonicalAutomatic (2 ^ h) (powerBase_ge_two h hh) (weightedCount t)

**Theorem 1.2 (weighted_not_lsdf_automatic).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.weighted_not_lsdf_automatic`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.weighted_not_lsdf_automatic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem weighted_not_lsdf_automatic {R : Type} [CommRing R] [Nontrivial R] [Fintype R] (t : R) (h : ℕ) (hh : 1 ≤ h) : ¬ IsKAutomaticSequence (2 ^ h) (weightedCount t)

**Theorem 1.3 (count_mod_not_canonical).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.count_mod_not_canonical`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.count_mod_not_canonical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem count_mod_not_canonical (q h : ℕ) (hq : 2 ≤ q) (hh : 1 ≤ h) : ¬ CanonicalAutomatic (2 ^ h) (powerBase_ge_two h hh) (fun n => count n % q)

**Theorem 1.4 (count_mod_not_lsdf).**

Lean statement: `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.count_mod_not_lsdf`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.count_mod_not_lsdf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Weighted halving partitions: extending Alekseyev (2026) and answering his Section 6 question negatively (p. 18, arXiv:2611.01243v1)*. URL: <https://github.com/the-omega-institute/trureturing-outreach/releases/tag/outreach-task-shortnote-e1da5d247e1d45546de554c29708119b>.

*Commentary.*

Exact source declaration: theorem count_mod_not_lsdf (q h : ℕ) (hq : 2 ≤ q) (hh : 1 ≤ h) : letI : NeZero q := ⟨by omega⟩; ¬ IsKAutomaticSequence (2 ^ h) (fun n => (count n : ZMod q))

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.count_mod_not_canonical`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.count_mod_not_lsdf`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.weighted_not_canonical_automatic`
- Truth anchor: `D5/S1/Recurrence/Partitions/HalvingPartitionAutomaticity.weighted_not_lsdf_automatic`
- Dependency: [D5/S0/Automata/CanonicalDFAOKernel](../../../S0/Automata/CanonicalDFAOKernel.md)
- Dependency: [D5/S1/Recurrence/KernelDecimation](../KernelDecimation.md)
- Dependency: [D5/S1/Recurrence/Partitions/HalvingPartitionWeightedNonregularity](HalvingPartitionWeightedNonregularity.md)
