# Partition

## Abstract

Partition

Selected live supplier declarations for the classical KS generator argument. Entropy is measured in nats. Finite partitions are measurable, cover the space and are pairwise disjoint modulo the probability law. The source port preserves the supplier hypotheses and the standard-axiom boundary; all helpers have actual downstream consumers. No mathematical novelty is claimed for the port.

**Definition 1.1 (entropy).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] (\mu : MeasureTheory.Measure \alpha) (s : \iota \to Set \alpha), D5.S3.Entropy.KolmogorovSinai.entropy \mu s = \sum i, (\mu (s i)).toReal.negMulLog$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Partition.entropy` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.2 (entropy def).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] (\mu : MeasureTheory.Measure \alpha) (s : \iota \to Set \alpha), D5.S3.Entropy.KolmogorovSinai.entropy \mu s = \sum i, (\mu (s i)).toReal.negMulLog$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_def` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.3 (MeasurePartition).**

$$\forall \{\alpha : Type\} [MeasurableSpace \alpha] (\mu : MeasureTheory.Measure \alpha) (\iota : Type) [Fintype \iota], MeasurePartition \mu \iota \equiv \{ cells : \iota \to Set \alpha // (\forall i, MeasurableSet (cells i)) \land Pairwise (AEDisjoint \mu on cells) \land (\operatorname{iUnion} i, cells i) = Set.univ \}$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Partition.MeasurePartition` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.4 (entropy nonneg).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] (\mu : MeasureTheory.Measure \alpha) [MeasureTheory.IsProbabilityMeasure \mu] (s : \iota \to Set \alpha), 0 \le D5.S3.Entropy.KolmogorovSinai.entropy \mu s$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_nonneg` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.5 (entropy le log card).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] [Nonempty \iota] (\mu : MeasureTheory.Measure \alpha) (s : \iota \to Set \alpha), \sum i, (\mu (s i)).toReal = 1 \to D5.S3.Entropy.KolmogorovSinai.entropy \mu s \le Real.log (Fintype.card \iota)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_le_log_card` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.6 (sum toReal measure eq one).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), \sum i, (\mu (P.cells i)).toReal = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.sum_toReal_measure_eq_one` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.7 (entropy le log card partition).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] [Nonempty \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.entropy \mu P.cells \le Real.log (Fintype.card \iota)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_le_log_card_partition` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.8 (joinCells).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\kappa : Type\} (s : \iota \to Set \alpha) (t : \kappa \to Set \alpha) (a : \iota \times \kappa), D5.S3.Entropy.KolmogorovSinai.joinCells s t a = s a.1 \operatorname{inter} t a.2$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Partition.joinCells` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.9 (joinCells apply).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\kappa : Type\} (s : \iota \to Set \alpha) (t : \kappa \to Set \alpha) (p : \iota \times \kappa), D5.S3.Entropy.KolmogorovSinai.joinCells s t p = s p.1 \operatorname{inter} t p.2$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.joinCells_apply` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.10 (measure eq sum inter).**

$$\forall \{\alpha : Type\} \{\kappa : Type\} [MeasurableSpace \alpha] [Fintype \kappa] \{\mu : MeasureTheory.Measure \alpha\} (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa) \{ A : Set \alpha\}, MeasurableSet A \to \mu A = \sum j, \mu (A \operatorname{inter} Q.cells j)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.measure_eq_sum_inter` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.11 (entropy join le).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\kappa : Type\} [MeasurableSpace \alpha] [Fintype \iota] [Fintype \kappa] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa), D5.S3.Entropy.KolmogorovSinai.entropy \mu (D5.S3.Entropy.KolmogorovSinai.joinCells P.cells Q.cells) \le D5.S3.Entropy.KolmogorovSinai.entropy \mu P.cells + D5.S3.Entropy.KolmogorovSinai.entropy \mu Q.cells$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_join_le` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.12 (condEntropy).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{ m\omega : MeasurableSpace \alpha\} [Fintype \iota] [StandardBorelSpace \alpha] (\mu : MeasureTheory.Measure \alpha) [MeasureTheory.IsFiniteMeasure \mu] (\mathcal{A} : MeasurableSpace \alpha) (s : \iota \to Set \alpha), D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} s = \int (omega : \alpha), \sum i, (((ProbabilityTheory.condExpKernel \mu \mathcal{A}) omega) (s i)).toReal.negMulLog \mathrm{d}\mu$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.13 (condEntropy def).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{ m\omega : MeasurableSpace \alpha\} [Fintype \iota] [StandardBorelSpace \alpha] (\mu : MeasureTheory.Measure \alpha) [MeasureTheory.IsFiniteMeasure \mu] (\mathcal{A} : MeasurableSpace \alpha) (s : \iota \to Set \alpha), D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} s = \int (omega : \alpha), \sum i, (((ProbabilityTheory.condExpKernel \mu \mathcal{A}) omega) (s i)).toReal.negMulLog \mathrm{d}\mu$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy_def` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.14 (negMulLog condExpKernel sum nonneg).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsFiniteMeasure \mu] (s : \iota \to Set \alpha) (omega : \alpha), 0 \le \sum i, (((ProbabilityTheory.condExpKernel \mu \mathcal{A}) omega) (s i)).toReal.negMulLog$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.negMulLog_condExpKernel_sum_nonneg` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.15 (condEntropy nonneg).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsFiniteMeasure \mu] \{ s : \iota \to Set \alpha\}, 0 \le D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} s$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy_nonneg` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.16 (integrable negMulLog condExpKernel).**

$$\forall \{\alpha : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsFiniteMeasure \mu], \mathcal{A} \le m\alpha \to \forall \{ A : Set \alpha\}, MeasurableSet A \to MeasureTheory.Integrable (\lambda omega \mapsto (((ProbabilityTheory.condExpKernel \mu \mathcal{A}) omega) A).toReal.negMulLog) \mu$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.integrable_negMulLog_condExpKernel` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.17 (integrable condEntropy integrand).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsFiniteMeasure \mu], \mathcal{A} \le m\alpha \to \forall (s : \iota \to Set \alpha), (\forall (i : \iota), MeasurableSet (s i)) \to MeasureTheory.Integrable (\lambda omega \mapsto \sum i, (((ProbabilityTheory.condExpKernel \mu \mathcal{A}) omega) (s i)).toReal.negMulLog) \mu$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.integrable_condEntropy_integrand` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.18 (condExpKernel sum toReal measure eq one).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu], \mathcal{A} \le m\alpha \to \forall (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), {\forall^{m}} (omega : \alpha) \mathrm{d}\mu, \sum i, (((ProbabilityTheory.condExpKernel \mu \mathcal{A}) omega) (P.cells i)).toReal = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.condExpKernel_sum_toReal_measure_eq_one` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.19 (condEntropy le log card).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] [Nonempty \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu], \mathcal{A} \le m\alpha \to \forall (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} P.cells \le Real.log (Fintype.card \iota)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy_le_log_card` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.20 (condEntropy join le).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\kappa : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] [Fintype \kappa] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu], \mathcal{A} \le m\alpha \to \forall (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa), D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} (D5.S3.Entropy.KolmogorovSinai.joinCells P.cells Q.cells) \le D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} P.cells + D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} Q.cells$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy_join_le` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.21 (condEntropyOnCell).**

$$\forall \{\alpha : Type\} \{\kappa : Type\} [m\alpha : MeasurableSpace \alpha] [Fintype \kappa] (\mu : MeasureTheory.Measure \alpha) (si : Set \alpha) (t : \kappa \to Set \alpha), D5.S3.Entropy.KolmogorovSinai.condEntropyOnCell \mu si t = \sum j, ((\mu (si \operatorname{inter} t j)).toReal / (\mu si).toReal).negMulLog$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropyOnCell` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.22 (condEntropyGivenPartition).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\kappa : Type\} [m\alpha : MeasurableSpace \alpha] [Fintype \iota] [Fintype \kappa] (\mu : MeasureTheory.Measure \alpha) (s : \iota \to Set \alpha) (t : \kappa \to Set \alpha), D5.S3.Entropy.KolmogorovSinai.condEntropyGivenPartition \mu s t = \sum i, (\mu (s i)).toReal \cdot D5.S3.Entropy.KolmogorovSinai.condEntropyOnCell \mu (s i) t$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropyGivenPartition` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.23 (entropy join eq add condEntropyGivenPartition).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\kappa : Type\} [m\alpha : MeasurableSpace \alpha] [Fintype \iota] [Fintype \kappa] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa), D5.S3.Entropy.KolmogorovSinai.entropy \mu (D5.S3.Entropy.KolmogorovSinai.joinCells P.cells Q.cells) = D5.S3.Entropy.KolmogorovSinai.entropy \mu P.cells + D5.S3.Entropy.KolmogorovSinai.condEntropyGivenPartition \mu P.cells Q.cells$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_join_eq_add_condEntropyGivenPartition` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.24 (condEntropy comap pullback).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] \{ T : \alpha \to \alpha\} [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu], \mathcal{A} \le m\alpha \to MeasureTheory.MeasurePreserving T \mu \mu \to \forall (n : \mathbb{N}) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), (D5.S3.Entropy.KolmogorovSinai.condEntropy \mu (MeasurableSpace.comap {T^{[n]}} \mathcal{A}) \lambda i \mapsto {{T^{[n]}}^{-1}}' P.cells i) = D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} P.cells$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy_comap_pullback` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

## References

- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.MeasurePartition`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropyGivenPartition`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropyOnCell`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy_comap_pullback`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy_def`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy_join_le`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy_le_log_card`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.condEntropy_nonneg`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.condExpKernel_sum_toReal_measure_eq_one`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.entropy`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_def`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_join_eq_add_condEntropyGivenPartition`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_join_le`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_le_log_card`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_le_log_card_partition`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.entropy_nonneg`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.integrable_condEntropy_integrand`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.integrable_negMulLog_condExpKernel`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.joinCells`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.joinCells_apply`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.measure_eq_sum_inter`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.negMulLog_condExpKernel_sum_nonneg`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/Partition.sum_toReal_measure_eq_one`
- Dependency: [D5/S3/Entropy/EntropyEquality](../EntropyEquality.md)
