# Generator

## Abstract

Generator

Selected live supplier declarations for the classical KS generator argument. Entropy is measured in nats. Finite partitions are measurable, cover the space and are pairwise disjoint modulo the probability law. The source port preserves the supplier hypotheses and the standard-axiom boundary; all helpers have actual downstream consumers. No mathematical novelty is claimed for the port.

**Theorem 1.1 (ksEntropyPartition le ksEntropySeq div).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) \{ n : \mathbb{N}\}, 1 \le n \to D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT P \le D5.S3.Entropy.KolmogorovSinai.ksEntropySeq hT P n / n$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Generator.ksEntropyPartition_le_ksEntropySeq_div` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.2 (ksEntropy eq ksEntropyPartition of generating).**

$$\forall \{\alpha : Type\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) \{ n : \mathbb{N}\} (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu (Fin n)), D5.S3.Entropy.KolmogorovSinai.IsGenerating \mu T P \to D5.S3.Entropy.KolmogorovSinai.ksEntropy hT = (D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT P)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Generator.ksEntropy_eq_ksEntropyPartition_of_generating` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

## References

- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Generator.ksEntropyPartition_le_ksEntropySeq_div`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Generator.ksEntropy_eq_ksEntropyPartition_of_generating`
- Dependency: [D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning](GeneratorConditioning.md)
