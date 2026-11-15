# Generator Conditioning

## Abstract

GeneratorConditioning

Selected live supplier declarations for the classical KS generator argument. Entropy is measured in nats. Finite partitions are measurable, cover the space and are pairwise disjoint modulo the probability law. The source port preserves the supplier hypotheses and the standard-axiom boundary; all helpers have actual downstream consumers. No mathematical novelty is claimed for the port.

**Theorem 1.1 (Finite partition conditioning and its generated sigma-algebra).**

Lean statement: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropyGivenPartition_eq_condEntropy_generated`

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropyGivenPartition_eq_condEntropy_generated` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

For every probability measure mu on a standard Borel measurable space, every finite measurable partition B, and every finite family t of measurable sets, condEntropyGivenPartition mu B.cells t equals condEntropy mu (generatedSigmaAlgebra mu B) t. The family t need not itself be a partition. Zero-mass B cells contribute zero. This is the existing finite-conditioning bridge, used by the finite-history rate envelope.

**Theorem 1.2 (generatedSigmaAlgebra le).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [m\alpha : MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} (B : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu B \le m\alpha$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.generatedSigmaAlgebra_le` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.3 (abramovRokhlin partition of defect).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\kappa : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} [Fintype \iota] [Fintype \kappa] (hm : \mathcal{A} \le m\alpha) (hT : MeasureTheory.MeasurePreserving T \mu \mu) (hinv : MeasurableSpace.comap T \mathcal{A} \le \mathcal{A}) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (g : (n : \mathbb{N}) \to (Fin n \to \iota) \to Fin n \to \kappa), (\forall (n : \mathbb{N}) (f : Fin n \to \iota), (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells f {\le^{m}}[\mu] (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q n).cells (g n f)) \to Filter.Tendsto (\lambda n \mapsto (D5.S3.Entropy.KolmogorovSinai.condEntropy \mu (D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q n)) (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells - D5.S3.Entropy.KolmogorovSinai.condKsEntropySeq \mathcal{A} hT P n) / n) Filter.atTop (nhds 0) \to D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT P = D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT Q + D5.S3.Entropy.KolmogorovSinai.condKsEntropyPartition hm hT hinv P$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.abramovRokhlin_partition_of_defect` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.4 (condEntropy ksJoin le nsmul log card).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{F} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] [Nonempty \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\}, \mathcal{F} \le m\alpha \to \forall (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (n : \mathbb{N}), D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{F} (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells \le n \cdot Real.log (Fintype.card \iota)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropy_ksJoin_le_nsmul_log_card` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.5 (condEntropy tendsto iSup).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] [Nonempty \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] (\mathcal{A}seq : \mathbb{N} \to MeasurableSpace \alpha), Monotone \mathcal{A}seq \to (\forall (n : \mathbb{N}), \mathcal{A}seq n \le m\alpha) \to \forall (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), Filter.Tendsto (\lambda n \mapsto D5.S3.Entropy.KolmogorovSinai.condEntropy \mu (\mathcal{A}seq n) P.cells) Filter.atTop (nhds (D5.S3.Entropy.KolmogorovSinai.condEntropy \mu (\operatorname{iSup} n, \mathcal{A}seq n) P.cells))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropy_tendsto_iSup` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.6 (generatedSigmaAlgebra ksJoin mono).**

$$\forall \{\alpha : Type\} \{\kappa : Type\} [m\alpha : MeasurableSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [Fintype \kappa] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa) \{ M n : \mathbb{N}\}, M \le n \to D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q M) \le D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.generatedSigmaAlgebra_ksJoin_mono` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.7 (comap iterate generatedSigmaAlgebra ksJoin le).**

$$\forall \{\alpha : Type\} \{\kappa : Type\} [m\alpha : MeasurableSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [Fintype \kappa] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa) (a b : \mathbb{N}), MeasurableSpace.comap {T^{[a]}} (D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q b)) \le D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q (a + b))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.comap_iterate_generatedSigmaAlgebra_ksJoin_le` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.8 (iSup generatedSigmaAlgebra ksJoin eq).**

$$\forall \{\alpha : Type\} \{\kappa : Type\} [m\alpha : MeasurableSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [Fintype \kappa] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa), \operatorname{iSup} n, D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q n) = \operatorname{iSup} k, MeasurableSpace.comap {T^{[k]}} (D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu Q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.iSup_generatedSigmaAlgebra_ksJoin_eq` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

## References

- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.abramovRokhlin_partition_of_defect`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.comap_iterate_generatedSigmaAlgebra_ksJoin_le`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropyGivenPartition_eq_condEntropy_generated`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropy_ksJoin_le_nsmul_log_card`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropy_tendsto_iSup`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.generatedSigmaAlgebra_ksJoin_mono`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.generatedSigmaAlgebra_le`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.iSup_generatedSigmaAlgebra_ksJoin_eq`
- Dependency: [D5/S3/Entropy/KolmogorovSinai/EntropyRate](EntropyRate.md)
