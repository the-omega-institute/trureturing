# Generator Conditioning

## Abstract

GeneratorConditioning

Selected live supplier declarations for the classical KS generator argument. Entropy is measured in nats. Finite partitions are measurable, cover the space and are pairwise disjoint modulo the probability law. The source port preserves the supplier hypotheses and the standard-axiom boundary; all helpers have actual downstream consumers. No mathematical novelty is claimed for the port.

A standard application is the stationary finite-history entropy bound. Let X be a standard Borel measurable space, mu a probability measure, T a measurable map preserving mu, and P a measurable finite partition indexed by I, with cells covering X and pairwise disjoint modulo mu. For j ≥ 0, write P_j(i) = (T^j)⁻¹(P(i)) and B_n(a) = ⋂_{0 ≤ j < n} P_j(a(j)) for a in I^{Fin n}. Thus B_0 is the one-cell partition of X and H_mu(B_0) = 0. Define the actual joint masses w_n(a,b) = mu.real(B_n(a) ∩ P_n(b)) and c_n = conditionalEntropy(w_n). Their row masses are mu.real(B_n(a)); a zero-mass row has zero conditional row and contributes zero, with 0 log 0 = 0. For n = 0, c_0 = H_mu(P). All entropies are in nats.

The existing finite-conditioning identity condEntropyGivenPartition_eq_condEntropy_generated identifies c_n with H_mu(P_n | sigma(B_n)). Both the history and next cell are pulled back by the same T under the same invariant law. The sigma-algebra of the shifted history is contained in sigma(B_{n+1}), as expressed by comap_iterate_generatedSigmaAlgebra_ksJoin_le; condEntropy_mono_of_le and condEntropy_comap_pullback therefore give c_{n+1} ≤ c_n. This uses joint pullback invariance, not merely equality of separate marginals, and requires no invariance assumption on the finite-history conditioning sigma-algebra.

The existing finite chain rule entropy_join_eq_add_condEntropyGivenPartition, together with the block reindexing ksJoinCells_append and entropy_reindex, gives H_mu(B_{n+1}) = H_mu(B_n) + c_n. Fix n ≥ 0 and put f(m) = H_mu(B_{n+m}) − m c_n. Since f(m+1) − f(m) = c_{n+m} − c_n ≤ 0, the usual successive-step criterion antitone_nat_of_succ_le gives f(m) ≤ f(0). Hence H_mu(B_{n+m}) ≤ H_mu(B_n) + m c_n for every m ≥ 0. Dividing by n+m > 0 gives H_mu(B_{n+m})/(n+m) ≤ c_n + (H_mu(B_n) − n c_n)/(n+m). The existing Fekete convergence tendsto_ksEntropySeq and the vanishing fixed boundary term yield h_mu(T,P) ≤ c_n for every n ≥ 0. This is a composition of standard stationary-process entropy results; it adds no Markov, ergodicity or assumed entropy-rate hypothesis.

Here h_mu(T,P) is the rate of this partition. Identifying it with the full KS supremum over finite partitions requires a separate generating-partition argument. A native symbolic-coordinate application must also supply the measurable partition and its exact iterate correspondence: for the bilateral Parry path coordinate J(r,t), this includes well-definedness and measurability of J, the cells P(i) = {r : J(r,0) = i}, and J(T^j r,t) = J(r,t+j) at every integer origin. The finite masses must then be those of the specified invariant law, including zero-probability histories and transitions. These native interfaces, the full KS supremum, and KS maximality and uniqueness are not established by the partition-rate derivation.

**Theorem 1.1 (generatedSigmaAlgebra le).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [m\alpha : MeasurableSpace \alpha] [Fintype \iota] \{\mu : MeasureTheory.Measure \alpha\} (B : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu B \le m\alpha$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.generatedSigmaAlgebra_le` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.2 (abramovRokhlin partition of defect).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\kappa : Type\} \{\mathcal{A} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\} [Fintype \iota] [Fintype \kappa] (hm : \mathcal{A} \le m\alpha) (hT : MeasureTheory.MeasurePreserving T \mu \mu) (hinv : MeasurableSpace.comap T \mathcal{A} \le \mathcal{A}) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (g : (n : \mathbb{N}) \to (Fin n \to \iota) \to Fin n \to \kappa), (\forall (n : \mathbb{N}) (f : Fin n \to \iota), (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells f {\le^{m}}[\mu] (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q n).cells (g n f)) \to Filter.Tendsto (\lambda n \mapsto (D5.S3.Entropy.KolmogorovSinai.condEntropy \mu (D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q n)) (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells - D5.S3.Entropy.KolmogorovSinai.condKsEntropySeq \mathcal{A} hT P n) / n) Filter.atTop (nhds 0) \to D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT P = D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition hT Q + D5.S3.Entropy.KolmogorovSinai.condKsEntropyPartition hm hT hinv P$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.abramovRokhlin_partition_of_defect` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.3 (condEntropy ksJoin le nsmul log card).**

$$\forall \{\alpha : Type\} \{\iota : Type\} \{\mathcal{F} : MeasurableSpace \alpha\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] [Nonempty \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] \{ T : \alpha \to \alpha\}, \mathcal{F} \le m\alpha \to \forall (hT : MeasureTheory.MeasurePreserving T \mu \mu) (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota) (n : \mathbb{N}), D5.S3.Entropy.KolmogorovSinai.condEntropy \mu \mathcal{F} (D5.S3.Entropy.KolmogorovSinai.ksJoin hT P n).cells \le n \cdot Real.log (Fintype.card \iota)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropy_ksJoin_le_nsmul_log_card` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.4 (condEntropy tendsto iSup).**

$$\forall \{\alpha : Type\} \{\iota : Type\} [m\alpha : MeasurableSpace \alpha] [StandardBorelSpace \alpha] [Fintype \iota] [Nonempty \iota] \{\mu : MeasureTheory.Measure \alpha\} [MeasureTheory.IsProbabilityMeasure \mu] (\mathcal{A}seq : \mathbb{N} \to MeasurableSpace \alpha), Monotone \mathcal{A}seq \to (\forall (n : \mathbb{N}), \mathcal{A}seq n \le m\alpha) \to \forall (P : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \iota), Filter.Tendsto (\lambda n \mapsto D5.S3.Entropy.KolmogorovSinai.condEntropy \mu (\mathcal{A}seq n) P.cells) Filter.atTop (nhds (D5.S3.Entropy.KolmogorovSinai.condEntropy \mu (\operatorname{iSup} n, \mathcal{A}seq n) P.cells))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropy_tendsto_iSup` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.5 (generatedSigmaAlgebra ksJoin mono).**

$$\forall \{\alpha : Type\} \{\kappa : Type\} [m\alpha : MeasurableSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [Fintype \kappa] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa) \{ M n : \mathbb{N}\}, M \le n \to D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q M) \le D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.generatedSigmaAlgebra_ksJoin_mono` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.6 (comap iterate generatedSigmaAlgebra ksJoin le).**

$$\forall \{\alpha : Type\} \{\kappa : Type\} [m\alpha : MeasurableSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [Fintype \kappa] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa) (a b : \mathbb{N}), MeasurableSpace.comap {T^{[a]}} (D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q b)) \le D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q (a + b))$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.comap_iterate_generatedSigmaAlgebra_ksJoin_le` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.7 (iSup generatedSigmaAlgebra ksJoin eq).**

$$\forall \{\alpha : Type\} \{\kappa : Type\} [m\alpha : MeasurableSpace \alpha] \{\mu : MeasureTheory.Measure \alpha\} [Fintype \kappa] \{ T : \alpha \to \alpha\} (hT : MeasureTheory.MeasurePreserving T \mu \mu) (Q : D5.S3.Entropy.KolmogorovSinai.MeasurePartition \mu \kappa), \operatorname{iSup} n, D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu (D5.S3.Entropy.KolmogorovSinai.ksJoin hT Q n) = \operatorname{iSup} k, MeasurableSpace.comap {T^{[k]}} (D5.S3.Entropy.KolmogorovSinai.generatedSigmaAlgebra \mu Q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.iSup_generatedSigmaAlgebra_ksJoin_eq` (`✓ std3`). ∎

*Citation.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

## References

- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.abramovRokhlin_partition_of_defect`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.comap_iterate_generatedSigmaAlgebra_ksJoin_le`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropy_ksJoin_le_nsmul_log_card`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.condEntropy_tendsto_iSup`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.generatedSigmaAlgebra_ksJoin_mono`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.generatedSigmaAlgebra_le`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/GeneratorConditioning.iSup_generatedSigmaAlgebra_ksJoin_eq`
- Dependency: [D5/S3/Entropy/KolmogorovSinai/EntropyRate](EntropyRate.md)
