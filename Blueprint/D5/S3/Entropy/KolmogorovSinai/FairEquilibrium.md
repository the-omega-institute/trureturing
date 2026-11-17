# Fair Equilibrium

## Abstract

FairEquilibrium

The coordinate partition generates the Borel sigma-algebra. The supplier generator theorem reduces the genuine KS supremum to its entropy rate. The entropy bound and the attained Bernoulli value are log 2. Equality forces the maximum entropy value for every finite-word distribution. Existing EntropyEquality gives uniform word masses; the cylinder pi-system determines the law. Measurable conjugacy transports both the invariant measure and the full KS supremum to positive source indices and symbols 1,2. Thus the same source-space fair law is the unique KS maximizer. No target existence or zero-deficit bridge is assumed.

**Definition 1.1 (fair).**

$$D5.S3.Entropy.SourceEquilibrium.fair = MeasureTheory.Measure.map D5.S3.Entropy.LopesOliveiraFullTail.coordinateEquiv (MeasureTheory.Measure.infinitePi (\lambda n : \mathbb{N} \mapsto (2 : ENNReal{)^{-1}} \cdot MeasureTheory.Measure.dirac false + (2 : ENNReal{)^{-1}} \cdot MeasureTheory.Measure.dirac true))$$

*Formalization.* `D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.2 (fair invariant).**

$$MeasureTheory.MeasurePreserving D5.S3.Entropy.LopesOliveiraFullTail.shift D5.S3.Entropy.SourceEquilibrium.fair D5.S3.Entropy.SourceEquilibrium.fair$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.3 (ks le).**

$$\forall (rho : MeasureTheory.Measure D5.S3.Entropy.LopesOliveiraFullTail.Omega) [MeasureTheory.IsProbabilityMeasure rho] (hT : MeasureTheory.MeasurePreserving D5.S3.Entropy.LopesOliveiraFullTail.shift rho rho), D5.S3.Entropy.KolmogorovSinai.ksEntropy hT \le (Real.log 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.ks_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.4 (fair ks).**

$$D5.S3.Entropy.KolmogorovSinai.ksEntropy D5.S3.Entropy.SourceEquilibrium.{fair_{invariant}} = (Real.log 2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair_ks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.5 (max unique).**

$$\forall (rho : MeasureTheory.Measure D5.S3.Entropy.LopesOliveiraFullTail.Omega) [MeasureTheory.IsProbabilityMeasure rho] (hT : MeasureTheory.MeasurePreserving D5.S3.Entropy.LopesOliveiraFullTail.shift rho rho), D5.S3.Entropy.KolmogorovSinai.ksEntropy hT = (Real.log 2) \to rho = D5.S3.Entropy.SourceEquilibrium.fair$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.max_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Marcel Morgenstern (2026). *Kolmogorov-Sinai entropy and Bernoulli shifts in Lean*. URL: <https://github.com/marcmorningstar/lean4-ergodic-theory/tree/040fec2e0ddf4fcba49af9f76c866d295308dd7f>.

*Commentary.*

The definitions and conventions in the introduction apply.

## References

- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair_invariant`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.fair_ks`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.ks_le`
- Truth anchor: `D5/S3/Entropy/KolmogorovSinai/FairEquilibrium.max_unique`
- Dependency: [D5/S3/Entropy/KolmogorovSinai/Bernoulli](Bernoulli.md)
- Dependency: [D5/S3/Entropy/LopesOliveiraFullTail](../LopesOliveiraFullTail.md)
