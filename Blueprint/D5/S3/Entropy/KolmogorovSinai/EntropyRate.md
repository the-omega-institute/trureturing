# Entropy Rate

## Abstract

EntropyRate

Selected live supplier declarations for the classical KS generator argument. Entropy is measured in nats. Finite partitions are measurable, cover the space and are pairwise disjoint modulo the probability law. The source port preserves the supplier hypotheses and the standard-axiom boundary; all helpers have actual downstream consumers. No mathematical novelty is claimed for the port.

**Theorem 1.1 (condEntropy mono of le).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} \mathcal{B} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu], \mathcal{A} \le \mathcal{B} \to \mathcal{B} \le m\alpha \to \forall (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{B} P.cells \le D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} P.cells$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condEntropy_mono_of_le` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.2 (pullback).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), (D5.S3.Entropy.KolmogorovSinai.MeasurePartition.pullback hT P).cells = \lambda i \mapsto {T^{-1}}' P.cells i$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.pullback` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.3 (pullback cells).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), (D5.S3.Entropy.KolmogorovSinai.MeasurePartition.pullback hT P).cells = \lambda i \mapsto {T^{-1}}' P.cells i$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.pullback_cells` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.4 (ksJoinCells).**

$$\forall \{\alpha : Type\} \{\iota : Type\} (cells : \iota \to Set \alpha) (T : \alpha \to \alpha) (n : \mathbb{N}) (f : Fin n \to \iota), D5.S3.Entropy.KolmogorovSinai.ksJoinCells cells T n f = \operatorname{Inter} k, {{T^{[k]}}^{-1}}' cells (f k)$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksJoinCells` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.5 (ksJoinCells apply).**

$$\forall \{\alpha : Type\} \{\iota : Type\} (cells : \iota \to Set \alpha) (T : \alpha \to \alpha) (n : \mathbb{N}) (f : Fin n \to \iota), D5.S3.Entropy.KolmogorovSinai.ksJoinCells cells T n f = \operatorname{Inter} k, {{T^{[k]}}^{-1}}' cells (f k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksJoinCells_apply` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.6 (ksJoin).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (n : \mathbb{N}), (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells = D5.S3.Entropy.KolmogorovSinai.ksJoinCells P.cells T n$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksJoin` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.7 (ksJoin cells).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (n : \mathbb{N}), (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells = D5.S3.Entropy.KolmogorovSinai.ksJoinCells P.cells T n$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksJoin_cells` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.8 (ksEntropySeq).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (n : \mathbb{N}), D5.S3.Entropy.KolmogorovSinai.ksEntropySeq hT P n = D5.S3.Entropy.KolmogorovSinai.entropy \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropySeq` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.9 (ksEntropySeq zero).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.ksEntropySeq hT P 0 = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropySeq_zero` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.10 (ksEntropySeq nonneg).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (n : \mathbb{N}), 0 \le D5.S3.Entropy.KolmogorovSinai.ksEntropySeq hT P n$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropySeq_nonneg` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.11 (entropy reindex).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\beta : Type\} [Fintype \beta] (\mu : MeasureTheory.Measure \alpha) (e : \iota \equiv \beta) (s : \beta \to Set \alpha), (D5.S3.Entropy.KolmogorovSinai.entropy \mu \lambda i \mapsto s (e i)) = D5.S3.Entropy.KolmogorovSinai.entropy \mu s$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.entropy_reindex` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.12 (ksJoinCells append).**

$$\forall \{\alpha : Type\} \{\iota : Type\} (cells : \iota \to Set \alpha) (T : \alpha \to \alpha) (n m : \mathbb{N}) (a : Fin n \to \iota) (b : Fin m \to \iota), D5.S3.Entropy.KolmogorovSinai.ksJoinCells cells T (n + m) (Fin.append a b) = D5.S3.Entropy.KolmogorovSinai.ksJoinCells cells T n a \operatorname{inter} {{T^{[n]}}^{-1}}' D5.S3.Entropy.KolmogorovSinai.ksJoinCells cells T m b$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksJoinCells_append` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.13 (ksSubadditive).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), Subadditive (D5.S3.Entropy.KolmogorovSinai.ksEntropySeq hT P)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksSubadditive` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.14 (ksEntropyPartition).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT P = sInf (Set.image (\lambda n : \mathbb{N} \mapsto D5.S3.Entropy.KolmogorovSinai.ksEntropySeq hT P n / n) (Set.Ici 1))$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropyPartition` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.15 (tendsto ksEntropySeq).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), Filter.Tendsto (\lambda n \mapsto D5.S3.Entropy.KolmogorovSinai.ksEntropySeq hT P n / n) Filter.atTop (nhds (D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT P))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.tendsto_ksEntropySeq` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.16 (ksEntropyPartition le entropy).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT P \le D5.S3.Entropy.KolmogorovSinai.entropy \mu P.cells$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropyPartition_le_entropy` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.17 (condKsEntropySeq).**

$$\forall \{\alpha : Type\} \{\iota : Type\} (\mathcal{A} : MeasurableSpace \alpha) [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (n : \mathbb{N}), D5.S3.Entropy.KolmogorovSinai.condKsEntropySeq \mathcal{A} hT P n = D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condKsEntropySeq` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.18 (condKsEntropyPartition).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hm : \mathcal{A} \le m\alpha) (hT : MeasureTheory.MeasurePreserving T \mu \mu) (hinv : MeasurableSpace.comap T \mathcal{A} \le \mathcal{A}) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.condKsEntropyPartition hm hT hinv P = sInf (Set.image (\lambda n : \mathbb{N} \mapsto D5.S3.Entropy.KolmogorovSinai.condKsEntropySeq \mathcal{A} hT P n / n) (Set.Ici 1))$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condKsEntropyPartition` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.19 (tendsto condKsEntropySeq).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hm : \mathcal{A} \le m\alpha) (hT : MeasureTheory.MeasurePreserving T \mu \mu) (hinv : MeasurableSpace.comap T \mathcal{A} \le \mathcal{A}) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), Filter.Tendsto (\lambda n \mapsto D5.S3.Entropy.KolmogorovSinai.condKsEntropySeq \mathcal{A} hT P n / n) Filter.atTop (nhds (D5.S3.Entropy.KolmogorovSinai.condKsEntropyPartition hm hT hinv P))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.tendsto_condKsEntropySeq` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.20 (condKsEntropyPartition nonneg).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hm : \mathcal{A} \le m\alpha) (hT : MeasureTheory.MeasurePreserving T \mu \mu) (hinv : MeasurableSpace.comap T \mathcal{A} \le \mathcal{A}) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), 0 \le D5.S3.Entropy.KolmogorovSinai.condKsEntropyPartition hm hT hinv P$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condKsEntropyPartition_nonneg` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.21 (condKsEntropyPartition le condEntropy).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hm : \mathcal{A} \le m\alpha) (hT : MeasureTheory.MeasurePreserving T \mu \mu) (hinv : MeasurableSpace.comap T \mathcal{A} \le \mathcal{A}) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.condKsEntropyPartition hm hT hinv P \le D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{A} P.cells$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condKsEntropyPartition_le_condEntropy` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.22 (ksEntropy).**

$$\forall \{\alpha : Type\} [MeasurableSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu), D5.S3.Entropy.KolmogorovSinai.ksEntropy hT = \operatorname{iSup} (n : \mathbb{N}), \operatorname{iSup} (P : MeasurePartition \mu (Fin n)), ((D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT P : \mathbb{R}) : EReal)$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropy` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.23 (le ksEntropy).**

$$\forall \{\alpha : Type\} [MeasurableSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) \{ n : \mathbb{N}\} (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu (Fin n)), (D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT P) \le D5.S3.Entropy.KolmogorovSinai.ksEntropy hT$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.le_ksEntropy` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.24 (pulledBack).**

$$\forall \{\alpha : Type\} \{\beta : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [MeasurableSpace \beta] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} \{\nu : MeasureTheory.Measure \beta\} \{\pi : \alpha \to \beta\} (h\pi : MeasureTheory.MeasurePreserving \pi \mu \nu) (R : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \nu \iota), (D5.S3.Entropy.KolmogorovSinai.MeasurePartition.pulledBack h\pi R).cells = \lambda i \mapsto {\pi^{-1}}' R.cells i$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.pulledBack` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.25 (factor relative eq).**

$$\forall \{\alpha : Type\} \{\beta : Type\} \{\iota : Type\} [MeasurableSpace \alpha] [MeasurableSpace \beta] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} \{\nu : MeasureTheory.Measure \beta\} [MeasureTheory.IsProbabilityMeasure \mu] [MeasureTheory.IsProbabilityMeasure \nu] \{ T : \alpha \to \alpha\} \{ S : \beta \to \beta\} \{\pi : \alpha \to \beta\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (hS : MeasureTheory.MeasurePreserving S \nu \nu) (h\pi : MeasureTheory.MeasurePreserving \pi \mu \nu), \pi \circ T = S \circ \pi \to \forall (R : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \nu \iota), D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT (D5.S3.Entropy.KolmogorovSinai.MeasurePartition.pulledBack h\pi R) = D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hS R$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.factor_relative_eq` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.26 (condCellSeq).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\kappa : Type\} [m\alpha : MeasurableSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} \{ T : \alpha \to \alpha\} [Fintype \iota] [Fintype \kappa] (hT : MeasureTheory.MeasurePreserving T \mu \mu) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (n : \mathbb{N}), D5.S3.Entropy.KolmogorovSinai.condCellSeq hT Q P n = D5.S3.Entropy.KolmogorovSinai.condEntropyGivenPartition \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q n).cells (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condCellSeq` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.27 (abramovRokhlin partition of W3).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\kappa : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] [StandardBorelSpace \alpha] \{ T : \alpha \to \alpha\} [Fintype \iota] [Fintype \kappa] (hm : \mathcal{A} \le m\alpha) (hT : MeasureTheory.MeasurePreserving T \mu \mu) (hinv : MeasurableSpace.comap T \mathcal{A} \le \mathcal{A}) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (g : (n : \mathbb{N}) \to (Fin n \to \iota) \to Fin n \to \kappa), (\forall (n : \mathbb{N}) (f : Fin n \to \iota), (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells f {\le^{m}}[\mu] (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q n).cells (g n f)) \to Filter.Tendsto (\lambda n \mapsto D5.S3.Entropy.KolmogorovSinai.condCellSeq hT Q P n / n) Filter.atTop (nhds (D5.S3.Entropy.KolmogorovSinai.condKsEntropyPartition hm hT hinv P)) \to D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT P = D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT Q + D5.S3.Entropy.KolmogorovSinai.condKsEntropyPartition hm hT hinv P$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/EntropyRate.abramovRokhlin_partition_of_W3` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.28 (generatedSigmaAlgebra).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [m\alpha : MeasurableSpace \alpha] [Fintype \iota] (\mu : MeasureTheory.Measure \alpha) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu P = MeasurableSpace.generateFrom (Set.range P.cells)$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.generatedSigmaAlgebra` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.29 (IsGenerating).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [m\alpha : MeasurableSpace \alpha] [Fintype \iota] (\mu : MeasureTheory.Measure \alpha) (T : \alpha \to \alpha) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.IsGenerating \mu T P = (\operatorname{iSup} n, MeasurableSpace.comap {T^{[n]}} (D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu P) = m\alpha)$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/EntropyRate.IsGenerating` (`✓ std3`).

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

## References

- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.IsGenerating`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.abramovRokhlin_partition_of_W3`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condCellSeq`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condEntropy_mono_of_le`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condKsEntropyPartition`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condKsEntropyPartition_le_condEntropy`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condKsEntropyPartition_nonneg`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.condKsEntropySeq`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.entropy_reindex`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.factor_relative_eq`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.generatedSigmaAlgebra`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropy`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropyPartition`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropyPartition_le_entropy`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropySeq`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropySeq_nonneg`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksEntropySeq_zero`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksJoin`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksJoinCells`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksJoinCells_append`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksJoinCells_apply`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksJoin_cells`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.ksSubadditive`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.le_ksEntropy`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.pullback`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.pullback_cells`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.pulledBack`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.tendsto_condKsEntropySeq`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/EntropyRate.tendsto_ksEntropySeq`
- Dependency: [D5/S3/Entropy/KolmogorovSinai/Partition](Partition.md)
