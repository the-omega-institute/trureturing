# Lopes Oliveira Full Tail

## Abstract

LopesOliveiraFullTail

The binary source space has positive indices and symbols 1,2. coordinateEquiv changes symbols false,true to 1,2 and index n to n+1. law gives equal mass to the all-1 sequence and to the sequence beginning with 2 followed by only 1. Their complete futures agree, so each first-symbol conditional probability is one half. Every Borel probability has bounded, integrable conditional-first entropy at most log 2. At the constant potential minus log 2, the all-law pressure and this law deficit are zero. The test function is one quarter of the second-symbol-1 indicator minus the first-symbol-1 indicator. Its integral is 1/8 under law and zero under every invariant probability. Its source-metric Lipschitz constant is at most one. Integrating against every actual coupling gives Wasserstein distance at least 1/8. This module supplies the obstruction; the KS target is proved in FairEquilibrium and the final assembly.

**Definition 1.1 (Symbol).**

$$Symbol=\{ j:\mathbb{N}|1\le j\land j\le2\}$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.Symbol` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.2 (Omega).**

$$D5.S3.Entropy.LopesOliveiraFullTail.Omega = D5.S3.Entropy.LopesOliveiraSource.Omega 2$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.Omega` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.3 (coordinateEquiv).**

$$\forall (x : \mathbb{N} \to Bool) (i : \mathbb{N}^{+}), (D5.S3.Entropy.LopesOliveiraFullTail.coordinateEquiv x i).val = if x i.natPred then 2 else 1$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.coordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.4 (shift).**

$$\forall (x : D5.S3.Entropy.LopesOliveiraFullTail.Omega), D5.S3.Entropy.LopesOliveiraFullTail.shift x = \lambda i : \mathbb{N}^{+} \mapsto x (i + 1)$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.shift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.5 (tailSigma).**

$$D5.S3.Entropy.LopesOliveiraFullTail.tailSigma = MeasurableSpace.comap D5.S3.Entropy.LopesOliveiraFullTail.shift inferInstance$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.tailSigma` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.6 (law).**

$$D5.S3.Entropy.LopesOliveiraFullTail.law = (2 : ENNReal{)^{-1}} \cdot MeasureTheory.Measure.dirac (D5.S3.Entropy.LopesOliveiraFullTail.coordinateEquiv (\lambda n : \mathbb{N} \mapsto false)) + (2 : ENNReal{)^{-1}} \cdot MeasureTheory.Measure.dirac (D5.S3.Entropy.LopesOliveiraFullTail.coordinateEquiv (\lambda n : \mathbb{N} \mapsto if n = 0 then true else false))$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.law` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.7 (firstIndicator).**

$$\forall (b : Bool) (x : D5.S3.Entropy.LopesOliveiraFullTail.Omega), D5.S3.Entropy.LopesOliveiraFullTail.firstIndicator b x = if D5.S3.Entropy.LopesOliveiraFullTail.coordinateEquiv.symm x 0 = b then 1 else 0$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.firstIndicator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.8 (sourceIndicator).**

$$\forall (j : D5.S3.Entropy.LopesOliveiraFullTail.Symbol) (x : D5.S3.Entropy.LopesOliveiraFullTail.Omega), D5.S3.Entropy.LopesOliveiraFullTail.sourceIndicator j x = if x 1 = j then 1 else 0$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.sourceIndicator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.9 (niEntropy).**

$$\forall (rho : MeasureTheory.Measure D5.S3.Entropy.LopesOliveiraFullTail.Omega), D5.S3.Entropy.LopesOliveiraFullTail.niEntropy rho = \int (x : D5.S3.Entropy.LopesOliveiraFullTail.Omega), \sum j, (rho[D5.S3.Entropy.LopesOliveiraFullTail.sourceIndicator j | D5.S3.Entropy.LopesOliveiraFullTail.tailSigma] x).negMulLog \mathrm{d}rho$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.niEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.10 (niPressure).**

$$\forall phi : D5.S3.Entropy.LopesOliveiraFullTail.Omega \to \mathbb{R}, D5.S3.Entropy.LopesOliveiraFullTail.niPressure phi = D5.S3.Entropy.LopesOliveiraSource.niPressure phi$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.niPressure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.11 (sourceDistance).**

$$\forall (x y : D5.S3.Entropy.LopesOliveiraFullTail.Omega), D5.S3.Entropy.LopesOliveiraFullTail.sourceDistance x y = dist (D5.S3.Entropy.LopesOliveiraFullTail.coordinateEquiv.symm x) (D5.S3.Entropy.LopesOliveiraFullTail.coordinateEquiv.symm y) / 2$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.sourceDistance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.12 (sourceMetric).**

$$\forall (x y : D5.S3.Entropy.LopesOliveiraFullTail.Omega), D5.S3.Entropy.LopesOliveiraFullTail.sourceMetric.toDist.dist x y = D5.S3.Entropy.LopesOliveiraFullTail.sourceDistance x y$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.sourceMetric` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.13 (couplings).**

$$\forall (eta xi : MeasureTheory.Measure D5.S3.Entropy.LopesOliveiraFullTail.Omega), D5.S3.Entropy.LopesOliveiraFullTail.couplings eta xi = \{ pi | MeasureTheory.IsProbabilityMeasure pi \land MeasureTheory.Measure.map Prod.fst pi = eta \land MeasureTheory.Measure.map Prod.snd pi = xi\}$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.couplings` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.14 (wassersteinOne).**

$$\forall (eta xi : MeasureTheory.Measure D5.S3.Entropy.LopesOliveiraFullTail.Omega), D5.S3.Entropy.LopesOliveiraFullTail.wassersteinOne eta xi = sInf \{ v | \exists pi \in D5.S3.Entropy.LopesOliveiraFullTail.couplings eta xi, v = \int (p : D5.S3.Entropy.LopesOliveiraFullTail.Omega \times D5.S3.Entropy.LopesOliveiraFullTail.Omega), D5.S3.Entropy.LopesOliveiraFullTail.sourceDistance p.1 p.2 \mathrm{d}pi\}$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraFullTail.wassersteinOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.15 (source distance eq).**

$$\forall (x y : D5.S3.Entropy.LopesOliveiraFullTail.Omega), D5.S3.Entropy.LopesOliveiraSource.distance x y = D5.S3.Entropy.LopesOliveiraFullTail.sourceDistance x y$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/LopesOliveiraFullTail.source_distance_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Theorem 1.16 (full tail transport obstruction).**

$$\forall (rho : MeasureTheory.Measure D5.S3.Entropy.LopesOliveiraFullTail.Omega) [MeasureTheory.IsProbabilityMeasure rho], MeasureTheory.Measure.map D5.S3.Entropy.LopesOliveiraFullTail.shift rho = rho \to borel D5.S3.Entropy.LopesOliveiraFullTail.Omega = inferInstance \land (\forall (x y : D5.S3.Entropy.LopesOliveiraFullTail.Omega), x \neq y \to D5.S3.Entropy.LopesOliveiraFullTail.sourceDistance x y = (1 / 2{)^{PiNat.firstDiff (D5.S3.Entropy.LopesOliveiraFullTail.coordinateEquiv.symm x) (D5.S3.Entropy.LopesOliveiraFullTail.coordinateEquiv.symm y) + 1}}) \land (\forall (eta : MeasureTheory.Measure D5.S3.Entropy.LopesOliveiraFullTail.Omega), MeasureTheory.IsProbabilityMeasure eta \to MeasureTheory.Integrable (\lambda x \mapsto \sum j, (eta[D5.S3.Entropy.LopesOliveiraFullTail.sourceIndicator j | D5.S3.Entropy.LopesOliveiraFullTail.tailSigma] x).negMulLog) eta) \land (D5.S3.Entropy.LopesOliveiraFullTail.niPressure \lambda x \mapsto -Real.log 2) = 0 \land D5.S3.Entropy.LopesOliveiraFullTail.niEntropy D5.S3.Entropy.LopesOliveiraFullTail.law = Real.log 2 \land (D5.S3.Entropy.LopesOliveiraFullTail.niPressure \lambda x \mapsto -Real.log 2) - D5.S3.Entropy.LopesOliveiraFullTail.niEntropy D5.S3.Entropy.LopesOliveiraFullTail.law - \int (x : D5.S3.Entropy.LopesOliveiraFullTail.Omega), -Real.log 2 \mathrm{d}D5.S3.Entropy.LopesOliveiraFullTail.law = 0 \land 1 / 8 \le D5.S3.Entropy.LopesOliveiraFullTail.wassersteinOne D5.S3.Entropy.LopesOliveiraFullTail.law rho$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/LopesOliveiraFullTail.full_tail_transport_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

## References

- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.Omega`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.Symbol`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.coordinateEquiv`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.couplings`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.firstIndicator`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.full_tail_transport_obstruction`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.law`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.niEntropy`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.niPressure`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.shift`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.sourceDistance`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.sourceIndicator`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.sourceMetric`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.source_distance_eq`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.tailSigma`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraFullTail.wassersteinOne`
- Dependency: [D5/S3/Entropy/LopesOliveiraSource](LopesOliveiraSource.md)
