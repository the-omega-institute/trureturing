# Bernoulli

## Abstract

Bernoulli

Selected live supplier declarations for the classical KS generator argument. Entropy is measured in nats. Finite partitions are measurable, cover the space and are pairwise disjoint modulo the probability law. The source port preserves the supplier hypotheses and the standard-axiom boundary; all helpers have actual downstream consumers. No mathematical novelty is claimed for the port.

**Definition 1.1 (Shift).**

$$\forall (\alpha : Type), D5.S3.Entropy.BernoulliShift.Shift \alpha = (\mathbb{N} \to \alpha)$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Bernoulli.Shift` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.2 (shiftMap).**

$$\forall \{{\alpha_{0}} : Type\} (a : D5.S3.Entropy.BernoulliShift.Shift {\alpha_{0}}), D5.S3.Entropy.BernoulliShift.shiftMap a = \lambda n \mapsto a (n + 1)$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Bernoulli.shiftMap` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.3 (measurable shiftMap).**

$$\forall \{{\alpha_{0}} : Type\} [MeasurableSpace {\alpha_{0}}], Measurable D5.S3.Entropy.BernoulliShift.shiftMap$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Bernoulli.measurable_shiftMap` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.4 (coordPartition).**

$$\forall \{{\alpha_{0}} : Type\} [Fintype {\alpha_{0}}] [MeasurableSpace {\alpha_{0}}] [MeasurableSingletonClass {\alpha_{0}}] (\mu : MeasureTheory.Measure (D5.S3.Entropy.BernoulliShift.Shift {\alpha_{0}})), (D5.S3.Entropy.BernoulliShift.coordPartition \mu).cells = \lambda i \mapsto \{ x | x 0 = i\}$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Bernoulli.coordPartition` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.5 (coordPartition isGenerating).**

$$\forall \{{\alpha_{0}} : Type\} [Fintype {\alpha_{0}}] [MeasurableSpace {\alpha_{0}}] [MeasurableSingletonClass {\alpha_{0}}] \{\mu : MeasureTheory.Measure (D5.S3.Entropy.BernoulliShift.Shift {\alpha_{0}})\}, MeasureTheory.MeasurePreserving D5.S3.Entropy.BernoulliShift.shiftMap \mu \mu \to D5.S3.Entropy.KolmogorovSinai.IsGenerating \mu D5.S3.Entropy.BernoulliShift.shiftMap (D5.S3.Entropy.BernoulliShift.coordPartition \mu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Bernoulli.coordPartition_isGenerating` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.6 (coordPartitionFin).**

$$\forall \{{\alpha_{0}} : Type\} [Fintype {\alpha_{0}}] [MeasurableSpace {\alpha_{0}}] [MeasurableSingletonClass {\alpha_{0}}] (\mu : MeasureTheory.Measure (D5.S3.Entropy.BernoulliShift.Shift {\alpha_{0}})), (D5.S3.Entropy.BernoulliShift.coordPartitionFin \mu).cells = \lambda j \mapsto (D5.S3.Entropy.BernoulliShift.coordPartition \mu).cells ((Fintype.equivFin {\alpha_{0}}).symm j)$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Bernoulli.coordPartitionFin` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.7 (generatedSigmaAlgebra coordPartitionFin eq).**

$$\forall \{{\alpha_{0}} : Type\} [Fintype {\alpha_{0}}] [MeasurableSpace {\alpha_{0}}] [MeasurableSingletonClass {\alpha_{0}}] \{\mu : MeasureTheory.Measure (D5.S3.Entropy.BernoulliShift.Shift {\alpha_{0}})\}, D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.BernoulliShift.coordPartitionFin \mu) = D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.BernoulliShift.coordPartition \mu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Bernoulli.generatedSigmaAlgebra_coordPartitionFin_eq` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.8 (ksEntropyPartition coordPartitionFin eq).**

$$\forall \{{\alpha_{0}} : Type\} [Fintype {\alpha_{0}}] [MeasurableSpace {\alpha_{0}}] [MeasurableSingletonClass {\alpha_{0}}] \{\mu : MeasureTheory.Measure (D5.S3.Entropy.BernoulliShift.Shift {\alpha_{0}})\} [MeasureTheory.IsProbabilityMeasure \mu] (h\sigma mp : MeasureTheory.MeasurePreserving D5.S3.Entropy.BernoulliShift.shiftMap \mu \mu), D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition h\sigma mp (D5.S3.Entropy.BernoulliShift.coordPartitionFin \mu) = D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition h\sigma mp (D5.S3.Entropy.BernoulliShift.coordPartition \mu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Bernoulli.ksEntropyPartition_coordPartitionFin_eq` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.9 (bern).**

$$\forall \{{\alpha_{0}} : Type\} [MeasurableSpace {\alpha_{0}}] (\nu : MeasureTheory.Measure {\alpha_{0}}), D5.S3.Entropy.BernoulliShift.bern \nu = MeasureTheory.Measure.infinitePi \lambda x \mapsto \nu$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Bernoulli.bern` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.10 (Hnu).**

$$\forall \{{\alpha_{0}} : Type\} [Fintype {\alpha_{0}}] [MeasurableSpace {\alpha_{0}}] (\nu : MeasureTheory.Measure {\alpha_{0}}), D5.S3.Entropy.BernoulliShift.Hnu \nu = \sum i, (\nu \{ i\}).toReal.negMulLog$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Bernoulli.Hnu` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.11 (measurePreserving shiftMap bern).**

$$\forall \{{\alpha_{0}} : Type\} [MeasurableSpace {\alpha_{0}}] (\nu : MeasureTheory.Measure {\alpha_{0}}) [MeasureTheory.IsProbabilityMeasure \nu], MeasureTheory.MeasurePreserving D5.S3.Entropy.BernoulliShift.shiftMap (D5.S3.Entropy.BernoulliShift.bern \nu) (D5.S3.Entropy.BernoulliShift.bern \nu)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Bernoulli.measurePreserving_shiftMap_bern` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.12 (ksJoinCells coordPartition eq).**

$$\forall \{{\alpha_{0}} : Type\} [Fintype {\alpha_{0}}] [MeasurableSpace {\alpha_{0}}] [MeasurableSingletonClass {\alpha_{0}}] (\nu : MeasureTheory.Measure {\alpha_{0}}) (n : \mathbb{N}) (f : Fin n \to {\alpha_{0}}), D5.S3.Entropy.KolmogorovSinai.ksJoinCells (D5.S3.Entropy.BernoulliShift.coordPartition (D5.S3.Entropy.BernoulliShift.bern \nu)).cells D5.S3.Entropy.BernoulliShift.shiftMap n f = \{ x | \forall (k : Fin n), x k = f k\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Bernoulli.ksJoinCells_coordPartition_eq` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.13 (bern ksJoinCells eq).**

$$\forall \{{\alpha_{0}} : Type\} [Fintype {\alpha_{0}}] [MeasurableSpace {\alpha_{0}}] [MeasurableSingletonClass {\alpha_{0}}] (\nu : MeasureTheory.Measure {\alpha_{0}}) [MeasureTheory.IsProbabilityMeasure \nu] (n : \mathbb{N}) (f : Fin n \to {\alpha_{0}}), (D5.S3.Entropy.BernoulliShift.bern \nu) (D5.S3.Entropy.KolmogorovSinai.ksJoinCells (D5.S3.Entropy.BernoulliShift.coordPartition (D5.S3.Entropy.BernoulliShift.bern \nu)).cells D5.S3.Entropy.BernoulliShift.shiftMap n f) = \prod k, \nu \{ f k\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Bernoulli.bern_ksJoinCells_eq` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.14 (ksEntropyPartition coordPartition bern eq).**

$$\forall \{{\alpha_{0}} : Type\} [Fintype {\alpha_{0}}] [MeasurableSpace {\alpha_{0}}] [MeasurableSingletonClass {\alpha_{0}}] (\nu : MeasureTheory.Measure {\alpha_{0}}) [MeasureTheory.IsProbabilityMeasure \nu], D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition (D5.S3.Entropy.BernoulliShift.{{measurePreserving_{shiftMap}}_{bern}} \nu) (D5.S3.Entropy.BernoulliShift.coordPartition (D5.S3.Entropy.BernoulliShift.bern \nu)) = D5.S3.Entropy.BernoulliShift.Hnu \nu$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Bernoulli.ksEntropyPartition_coordPartition_bern_eq` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

## References

- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.Hnu`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.Shift`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.bern`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.bern_ksJoinCells_eq`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.coordPartition`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.coordPartitionFin`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.coordPartition_isGenerating`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.generatedSigmaAlgebra_coordPartitionFin_eq`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.ksEntropyPartition_coordPartitionFin_eq`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.ksEntropyPartition_coordPartition_bern_eq`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.ksJoinCells_coordPartition_eq`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.measurable_shiftMap`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.measurePreserving_shiftMap_bern`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Bernoulli.shiftMap`
- Dependency: [D5/S3/Entropy/KolmogorovSinai/Generator](Generator.md)
