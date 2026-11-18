# Lopes Oliveira Source

## Abstract

LopesOliveiraSource

Coordinates are positive integers and symbols are exactly 1 through d. The distance is one half the zero-based PiNat distance, hence 2 to the negative first differing source index. The metric retains the product topology, whose Borel sigma-algebra is the product measurable space. tailSigma is the pullback of that entire Borel sigma-algebra by the left shift, not a remote-tail intersection. niEntropy uses canonical conditional expectations of first-symbol indicators and natural logarithms with the zero endpoint convention. niPressure takes the supremum over all Borel probability laws. The coupling infimum uses the actual source metric. IsHolder permits every positive exponent and every nonnegative finite Holder constant.

**Definition 1.1 (Symbol).**

$$\forall (d:\mathbb{N}), Symbol d=\{ j:\mathbb{N}|1\le j\land j\le d\}$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.Symbol` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.2 (Omega).**

$$\forall (d : \mathbb{N}), D5.S3.Entropy.LopesOliveiraSource.Omega d = (\mathbb{N}^{+} \to D5.S3.Entropy.LopesOliveiraSource.Symbol d)$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.Omega` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.3 (shift).**

$$\forall \{ d : \mathbb{N}\} (x : D5.S3.Entropy.LopesOliveiraSource.Omega d), D5.S3.Entropy.LopesOliveiraSource.shift x = \lambda i : \mathbb{N}^{+} \mapsto x (i + 1)$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.shift` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.4 (tailSigma).**

$$\forall \{ d : \mathbb{N}\}, D5.S3.Entropy.LopesOliveiraSource.tailSigma = MeasurableSpace.comap D5.S3.Entropy.LopesOliveiraSource.shift inferInstance$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.tailSigma` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.5 (firstIndicator).**

$$\forall \{ d : \mathbb{N}\} (j : D5.S3.Entropy.LopesOliveiraSource.Symbol d) (x : D5.S3.Entropy.LopesOliveiraSource.Omega d), D5.S3.Entropy.LopesOliveiraSource.firstIndicator j x = if x 1 = j then 1 else 0$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.firstIndicator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.6 (niEntropy).**

$$\forall \{ d : \mathbb{N}\} (rho : MeasureTheory.Measure (D5.S3.Entropy.LopesOliveiraSource.Omega d)), D5.S3.Entropy.LopesOliveiraSource.niEntropy rho = \int (x : D5.S3.Entropy.LopesOliveiraSource.Omega d), \sum j, (rho[D5.S3.Entropy.LopesOliveiraSource.firstIndicator j | D5.S3.Entropy.LopesOliveiraSource.tailSigma] x).negMulLog \mathrm{d}rho$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.niEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.7 (niPressure).**

$$\forall \{ d : \mathbb{N}\} (phi : D5.S3.Entropy.LopesOliveiraSource.Omega d \to \mathbb{R}), D5.S3.Entropy.LopesOliveiraSource.niPressure phi = sSup \{ v | \exists rho, MeasureTheory.IsProbabilityMeasure rho \land v = \int (x : D5.S3.Entropy.LopesOliveiraSource.Omega d), phi x \mathrm{d}rho + D5.S3.Entropy.LopesOliveiraSource.niEntropy rho\}$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.niPressure` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.8 (distance).**

$$\forall \{ d : \mathbb{N}\} (x y : D5.S3.Entropy.LopesOliveiraSource.Omega d), D5.S3.Entropy.LopesOliveiraSource.distance x y = dist (\lambda n : \mathbb{N} \mapsto x (Nat.succPNat n)) (\lambda n : \mathbb{N} \mapsto y (Nat.succPNat n)) / 2$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.distance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.9 (sourceMetric).**

$$\forall (d : \mathbb{N}) (x y : D5.S3.Entropy.LopesOliveiraSource.Omega d), (D5.S3.Entropy.LopesOliveiraSource.sourceMetric d).toDist.dist x y = D5.S3.Entropy.LopesOliveiraSource.distance x y$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.sourceMetric` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.10 (couplings).**

$$\forall \{ d : \mathbb{N}\} (eta xi : MeasureTheory.Measure (D5.S3.Entropy.LopesOliveiraSource.Omega d)), D5.S3.Entropy.LopesOliveiraSource.couplings eta xi = \{ pi | MeasureTheory.IsProbabilityMeasure pi \land MeasureTheory.Measure.map Prod.fst pi = eta \land MeasureTheory.Measure.map Prod.snd pi = xi\}$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.couplings` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.11 (wassersteinOne).**

$$\forall \{ d : \mathbb{N}\} (eta xi : MeasureTheory.Measure (D5.S3.Entropy.LopesOliveiraSource.Omega d)), D5.S3.Entropy.LopesOliveiraSource.wassersteinOne eta xi = sInf \{ v | \exists pi \in D5.S3.Entropy.LopesOliveiraSource.couplings eta xi, v = \int (p : D5.S3.Entropy.LopesOliveiraSource.Omega d \times D5.S3.Entropy.LopesOliveiraSource.Omega d), D5.S3.Entropy.LopesOliveiraSource.distance p.1 p.2 \mathrm{d}pi\}$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.wassersteinOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

**Definition 1.12 (IsHolder).**

$$\forall \{ d : \mathbb{N}\} (phi : D5.S3.Entropy.LopesOliveiraSource.Omega d \to \mathbb{R}), D5.S3.Entropy.LopesOliveiraSource.IsHolder phi = \exists alpha, 0 < alpha \land \exists H, 0 \le H \land \forall (x y : D5.S3.Entropy.LopesOliveiraSource.Omega d), |phi x - phi y| \le H \cdot {(D5.S3.Entropy.LopesOliveiraSource.distance x y)}^{alpha}$$

*Formalization.* `D5/S3/Entropy/LopesOliveiraSource.IsHolder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Artur O. Lopes and Elismar R. Oliveira (2026). *Thermodynamic Formalism for Non-Invariant Probabilities: Entropy, Divergence, Channels*. URL: <https://arxiv.org/html/2611.13904v1#S8>.

*Commentary.*

The definitions and conventions in the introduction apply.

## References

- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.IsHolder`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.Omega`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.Symbol`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.couplings`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.distance`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.firstIndicator`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.niEntropy`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.niPressure`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.shift`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.sourceMetric`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.tailSigma`
- Truth anchor: `D5/S3/Entropy/LopesOliveiraSource.wassersteinOne`
