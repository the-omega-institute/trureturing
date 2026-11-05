# A Gaussian-mixture counterexample to covariance-corrected entropy uncertainty

## Abstract

An equal mixture of two displaced coherent states violates the covariance-corrected quadrature entropy inequality in units with Planck's constant equal to one.

**Definition 1.1 (The one-mode Gaussian Wigner density).**

$$\forall (\operatorname{\mu x}: \mathbb{R}), (\forall (\operatorname{\mu p}: \mathbb{R}), (\forall (a: \mathbb{R}), (\forall (b: \mathbb{R}), (\forall (c: \mathbb{R}), (\forall (x: \mathbb{R}), (\forall (p: \mathbb{R}), (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.gaussianWigner}\left(\operatorname{\mu x}, \operatorname{\mu p}, a, b, c, x, p\right) = (\operatorname{Inv.inv}\left(((2) \cdot (\operatorname{Real.pi})) \cdot (\operatorname{Real.sqrt}\left((a) \cdot (c) - (b)^{(2: \mathbb{N})}\right))\right)) \cdot (\operatorname{Real.exp}\left(\frac{-((c) \cdot ((x - \operatorname{\mu x})^{(2: \mathbb{N})}) - (((2) \cdot (b)) \cdot (x - \operatorname{\mu x})) \cdot (p - \operatorname{\mu p}) + (a) \cdot ((p - \operatorname{\mu p})^{(2: \mathbb{N})}))}{(2) \cdot ((a) \cdot (c) - (b)^{(2: \mathbb{N})})}\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.gaussianWigner` (`✓ std3`).

*Citation.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

The mean is (μx, μp), and the covariance matrix has diagonal entries a and c and off-diagonal entry b. Its determinant is ac − b². For a > 0, c > 0 and ac − b² ≥ 1/4, this is the normalized Wigner density of a physical one-mode Gaussian state with Planck's constant equal to one. The defining expression itself is a total real function and imposes none of those inequalities. The covariance convention is that of Section II.A of Hertz, Jabbour and Cerf, arXiv:1702.07286v2, EP-Unc-Rel-8.tex, lines 108–117.

**Definition 1.2 (The position marginal).**

$$\forall (W: (\mathbb{R}) \to ((\mathbb{R}) \to (\mathbb{R}))), (\forall (x: \mathbb{R}), (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalX}\left(W, x\right) = \int_{(p: \mathbb{R})} (W\left(x, p\right)) \mathrm{d} \operatorname{MeasureTheory.MeasureSpace.volume}))$$

*Formalization.* `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.marginalX` (`✓ std3`).

*Citation.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

Integrating W over p gives its x marginal. For a Wigner function this is the probability density of the x quadrature, as in Section II.B, EP-Unc-Rel-8.tex, line 161. The definition takes any real function W of two real variables.

**Definition 1.3 (The momentum marginal).**

$$\forall (W: (\mathbb{R}) \to ((\mathbb{R}) \to (\mathbb{R}))), (\forall (p: \mathbb{R}), (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalP}\left(W, p\right) = \int_{(x: \mathbb{R})} (W\left(x, p\right)) \mathrm{d} \operatorname{MeasureTheory.MeasureSpace.volume}))$$

*Formalization.* `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.marginalP` (`✓ std3`).

*Citation.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

Integrating W over x gives its p marginal. For a Wigner function this is the probability density of the p quadrature, as in Section II.B, EP-Unc-Rel-8.tex, line 161. All integrals here use Lebesgue volume.

**Definition 1.4 (Differential entropy).**

$$\forall (f: (\mathbb{R}) \to (\mathbb{R})), (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.densityEntropy}\left(f\right) = -(\int_{(x: \mathbb{R})} ((f\left(x\right)) \cdot (\operatorname{Real.log}\left((f\left(x\right))\right))) \mathrm{d} \operatorname{MeasureTheory.MeasureSpace.volume}))$$

*Formalization.* `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.densityEntropy` (`✓ std3`).

*Citation.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

Differential entropy is minus the integral of f times its natural logarithm. This is the convention in Section II.B, EP-Unc-Rel-8.tex, lines 155–159. The expression is defined for every real function f; the uncertainty statement separately requires integrability of the entropy integrands.

**Definition 1.5 (The first position moment).**

$$\forall (W: (\mathbb{R}) \to ((\mathbb{R}) \to (\mathbb{R}))), (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.meanX}\left(W\right) = \int_{(r: \mathbb{R} \times \mathbb{R})} ((r.1) \cdot (W\left(r.1, r.2\right))) \mathrm{d} \operatorname{MeasureTheory.MeasureSpace.volume})$$

*Formalization.* `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.meanX` (`✓ std3`).

*Citation.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

The position mean is the phase-space integral of the first coordinate against W. For a normalized Wigner density this represents the quadrature mean used in Section II.A, EP-Unc-Rel-8.tex, line 108.

**Definition 1.6 (The first momentum moment).**

$$\forall (W: (\mathbb{R}) \to ((\mathbb{R}) \to (\mathbb{R}))), (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.meanP}\left(W\right) = \int_{(r: \mathbb{R} \times \mathbb{R})} ((r.2) \cdot (W\left(r.1, r.2\right))) \mathrm{d} \operatorname{MeasureTheory.MeasureSpace.volume})$$

*Formalization.* `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.meanP` (`✓ std3`).

*Citation.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

The momentum mean is the phase-space integral of the second coordinate against W. It represents the second quadrature mean in Section II.A, EP-Unc-Rel-8.tex, line 108.

**Definition 1.7 (The central position second moment).**

$$\forall (W: (\mathbb{R}) \to ((\mathbb{R}) \to (\mathbb{R}))), (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covarianceXX}\left(W\right) = \int_{(r: \mathbb{R} \times \mathbb{R})} (((r.1 - \operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.meanX}\left(W\right))^{(2: \mathbb{N})}) \cdot (W\left(r.1, r.2\right))) \mathrm{d} \operatorname{MeasureTheory.MeasureSpace.volume})$$

*Formalization.* `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.covarianceXX` (`✓ std3`).

*Citation.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

The position variance is the integral of the squared deviation from meanX W against W. This is the central-moment convention of Section II.A, EP-Unc-Rel-8.tex, lines 108–116, expressed on phase space.

**Definition 1.8 (The central momentum second moment).**

$$\forall (W: (\mathbb{R}) \to ((\mathbb{R}) \to (\mathbb{R}))), (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covariancePP}\left(W\right) = \int_{(r: \mathbb{R} \times \mathbb{R})} (((r.2 - \operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.meanP}\left(W\right))^{(2: \mathbb{N})}) \cdot (W\left(r.1, r.2\right))) \mathrm{d} \operatorname{MeasureTheory.MeasureSpace.volume})$$

*Formalization.* `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.covariancePP` (`✓ std3`).

*Citation.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

The momentum variance is the integral of the squared deviation from meanP W against W. It is the second diagonal entry of the covariance matrix in Section II.A, EP-Unc-Rel-8.tex, lines 108–116.

**Definition 1.9 (The central cross moment).**

$$\forall (W: (\mathbb{R}) \to ((\mathbb{R}) \to (\mathbb{R}))), (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covarianceXP}\left(W\right) = \int_{(r: \mathbb{R} \times \mathbb{R})} (((r.1 - \operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.meanX}\left(W\right)) \cdot (r.2 - \operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.meanP}\left(W\right))) \cdot (W\left(r.1, r.2\right))) \mathrm{d} \operatorname{MeasureTheory.MeasureSpace.volume})$$

*Formalization.* `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.covarianceXP` (`✓ std3`).

*Citation.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

The cross covariance integrates the product of the two centered coordinates against W. For a Wigner function this is the symmetrized quadrature covariance defined in Section II.A, EP-Unc-Rel-8.tex, line 117.

**Definition 1.10 (The covariance-corrected inequality for finite Gaussian mixtures).**

$$(\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (w: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (\operatorname{\mu x}: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (\operatorname{\mu p}: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (a: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (b: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (c: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), ((\forall (i: \operatorname{Fin}\left(n\right)), (0 \le w\left(i\right))) \Rightarrow ((\sum_{(i: \operatorname{Fin}\left(n\right))} (w\left(i\right)) = 1) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (0 < a\left(i\right))) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (0 < c\left(i\right))) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (\frac{1}{4} \le (a\left(i\right)) \cdot (c\left(i\right)) - (b\left(i\right))^{(2: \mathbb{N})})) \Rightarrow (\operatorname{let} (W: (\mathbb{R}) \to ((\mathbb{R}) \to (\mathbb{R}))) := (\lambda (x: \mathbb{R}) \mapsto (\lambda (p: \mathbb{R}) \mapsto (\operatorname{D5.S3.Entropy.Mixing.MixtureEntropyBracket.mixture}\left(w, (\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\lambda (y: \mathbb{R}) \mapsto (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.gaussianWigner}\left(\operatorname{\mu x}\left(i\right), \operatorname{\mu p}\left(i\right), a\left(i\right), b\left(i\right), c\left(i\right), y, p\right)))), x\right)))); ((\operatorname{MeasureTheory.Integrable}\left((\lambda (x: \mathbb{R}) \mapsto ((\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalX}\left(W, x\right)) \cdot (\operatorname{Real.log}\left((\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalX}\left(W, x\right))\right)))), \operatorname{MeasureTheory.MeasureSpace.volume}\right)) \Rightarrow ((\operatorname{MeasureTheory.Integrable}\left((\lambda (p: \mathbb{R}) \mapsto ((\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalP}\left(W, p\right)) \cdot (\operatorname{Real.log}\left((\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalP}\left(W, p\right))\right)))), \operatorname{MeasureTheory.MeasureSpace.volume}\right)) \Rightarrow ((\operatorname{MeasureTheory.Integrable}\left((\lambda (r: \mathbb{R} \times \mathbb{R}) \mapsto (((r.1)^{(2: \mathbb{N})} + (r.2)^{(2: \mathbb{N})}) \cdot (W\left(r.1, r.2\right)))), \operatorname{MeasureTheory.MeasureSpace.volume}\right)) \Rightarrow (\operatorname{Real.log}\left(((\operatorname{Real.pi}) \cdot (\operatorname{Real.exp}\left(1\right)))\right) \le \operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.densityEntropy}\left(\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalX}\left(W\right)\right) + \operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.densityEntropy}\left(\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalP}\left(W\right)\right) - (\frac{1}{2}) \cdot (\operatorname{Real.log}\left((\frac{(\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covarianceXX}\left(W\right)) \cdot (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covariancePP}\left(W\right))}{(\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covarianceXX}\left(W\right)) \cdot (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covariancePP}\left(W\right)) - (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covarianceXP}\left(W\right))^{(2: \mathbb{N})}})\right)))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

Section III.B, EP-Unc-Rel-8.tex, lines 281–290, proposes subtracting the Gaussian mutual information from the sum of the two quadrature entropies and bounding the difference below by ln(πeℏ). The all-state assertion is conditional in the source; Section III.C, lines 334–341 and 455–456, assumes concavity of the uncertainty functional to extend the argument to mixed states. Here ℏ = 1 and the assertion ranges over finite mixtures of physical one-mode Gaussian densities. The weights are nonnegative and sum to one; a and c are positive, and each component determinant is at least 1/4. The two entropy integrands and the phase-space second-moment integrand must be integrable. There is no separate assumption n > 0: normalization rules out the empty mixture. This class is contained in the source's all-state class, so a failure in this class disproves that universal reading.

**Theorem 1.11 (Two oppositely displaced coherent states violate the inequality).**

$$\neg (\forall (n: \mathbb{N}), (\forall (w: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (\operatorname{\mu x}: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (\operatorname{\mu p}: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (a: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (b: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), (\forall (c: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), ((\forall (i: \operatorname{Fin}\left(n\right)), (0 \le w\left(i\right))) \Rightarrow ((\sum_{(i: \operatorname{Fin}\left(n\right))} (w\left(i\right)) = 1) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (0 < a\left(i\right))) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (0 < c\left(i\right))) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (\frac{1}{4} \le (a\left(i\right)) \cdot (c\left(i\right)) - (b\left(i\right))^{(2: \mathbb{N})})) \Rightarrow (\operatorname{let} (W: (\mathbb{R}) \to ((\mathbb{R}) \to (\mathbb{R}))) := (\lambda (x: \mathbb{R}) \mapsto (\lambda (p: \mathbb{R}) \mapsto (\operatorname{D5.S3.Entropy.Mixing.MixtureEntropyBracket.mixture}\left(w, (\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\lambda (y: \mathbb{R}) \mapsto (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.gaussianWigner}\left(\operatorname{\mu x}\left(i\right), \operatorname{\mu p}\left(i\right), a\left(i\right), b\left(i\right), c\left(i\right), y, p\right)))), x\right)))); ((\operatorname{MeasureTheory.Integrable}\left((\lambda (x: \mathbb{R}) \mapsto ((\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalX}\left(W, x\right)) \cdot (\operatorname{Real.log}\left((\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalX}\left(W, x\right))\right)))), \operatorname{MeasureTheory.MeasureSpace.volume}\right)) \Rightarrow ((\operatorname{MeasureTheory.Integrable}\left((\lambda (p: \mathbb{R}) \mapsto ((\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalP}\left(W, p\right)) \cdot (\operatorname{Real.log}\left((\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalP}\left(W, p\right))\right)))), \operatorname{MeasureTheory.MeasureSpace.volume}\right)) \Rightarrow ((\operatorname{MeasureTheory.Integrable}\left((\lambda (r: \mathbb{R} \times \mathbb{R}) \mapsto (((r.1)^{(2: \mathbb{N})} + (r.2)^{(2: \mathbb{N})}) \cdot (W\left(r.1, r.2\right)))), \operatorname{MeasureTheory.MeasureSpace.volume}\right)) \Rightarrow (\operatorname{Real.log}\left(((\operatorname{Real.pi}) \cdot (\operatorname{Real.exp}\left(1\right)))\right) \le \operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.densityEntropy}\left(\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalX}\left(W\right)\right) + \operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.densityEntropy}\left(\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.marginalP}\left(W\right)\right) - (\frac{1}{2}) \cdot (\operatorname{Real.log}\left((\frac{(\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covarianceXX}\left(W\right)) \cdot (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covariancePP}\left(W\right))}{(\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covarianceXX}\left(W\right)) \cdot (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covariancePP}\left(W\right)) - (\operatorname{D5.S3.Quantum.Measurements.EntropyPowerCovarianceUncertaintyRefutation.covarianceXP}\left(W\right))^{(2: \mathbb{N})}})\right)))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hertz-jabbour-cerf-2017-covariance-corrected-entropy-power-uncertainty` (refuted) by `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hertz-jabbour-cerf-2017-covariance-corrected-entropy-power-uncertainty","declaration_gid":"D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf (2017). *Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states*. DOI: [10.1088/1751-8121/aa852f](https://doi.org/10.1088/1751-8121/aa852f). URL: <https://arxiv.org/abs/1702.07286v2>.

*Commentary.*

For a real displacement d, let gₘ be the normal density with mean m and variance 1/2. Consider the equal mixture of the Gaussian Wigner densities with means (d,d) and (−d,−d), each having a = c = 1/2 and b = 0. Each component factors as gᵤ(x)gᵥ(p) at its mean (u,v): substituting the covariance entries gives the normalization 1/π and exponent −(x−u)² − (p−v)².

The Gaussian moment integrals are ∫x gₘ(x) dx = m and ∫x² gₘ(x) dx = m² + 1/2, and the centered second moment is 1/2; the first- and second-moment integrands are integrable. These follow from the Gaussian density moments and the variance of the Gaussian measure. Also ln gₘ(x) = −(ln π)/2 − (x−m)². Integrating this identity against gₘ gives an integrable entropy integrand and entropy (ln(πe))/2.

For nonnegative real numbers A and B, monotonicity of the logarithm gives A(ln A − ln 2) ≤ A ln((A+B)/2), treating A = 0 separately. Adding the corresponding inequality with A and B interchanged bounds −((A+B)/2) ln((A+B)/2) above by −(A ln A + B ln B)/2 + ((A+B)/2) ln 2. For normalized nonnegative densities f and g with the three entropy integrands integrable, integrating yields h((f+g)/2) ≤ (h(f)+h(g))/2 + ln 2.

To justify integrability for the equal mixture of g_d and g_−d, each Gaussian is continuous, nonnegative and at most one, as follows from its logarithm. Their average therefore lies between zero and one, and its product with its logarithm is measurable and nonpositive. The pointwise bound just proved dominates the absolute value of that product by an integrable combination of the two Gaussian entropy integrands and the average density. Thus both marginal entropy integrands are integrable.

Integrating the factored components in either coordinate shows that both marginals are (g_d + g_−d)/2. More generally, integrating a product f(x)g(p) against the two-component phase-space mixture gives the average of the products of its one-dimensional component integrals. The product-integral identity also gives integrability whenever the four component integrands are integrable. Applying it to the constant, linear and squared coordinate functions gives zero means, covarianceXX = covariancePP = d² + 1/2, and covarianceXP = d². Adding the two integrable squared-coordinate terms verifies the required phase-space second-moment integrability.

The binary entropy estimate and the Gaussian entropy formula now give h(W_x) + h(W_p) ≤ ln(πe) + 2 ln 2. At d = 6 the covariance ratio is ((36 + 1/2)²)/((36 + 1/2)² − 36²) = 5329/145. Since 16 < 5329/145, logarithm monotonicity and ln 16 = 4 ln 2 give 2 ln 2 < (ln(5329/145))/2.

Assume the universal inequality. Set n = 2, take both weights to be 1/2, set μx = μp to the vector (6,−6), and take the constant covariance families a = c = 1/2 and b = 0. The weights normalize, and each component determinant equals 1/4. The finite sum is precisely the equal mixture above. Substitute its marginals, the verified integrability conditions and its covariance entries into the assumed inequality. It requires ln(πe) ≤ h(W_x) + h(W_p) − (ln(5329/145))/2, whereas the entropy upper bound and the strict logarithmic estimate make the right-hand side smaller than ln(πe). This contradiction proves the negation of the universal statement.

The counterexample consists of mixed states with positive Wigner functions. The statement for pure states, the joint Wigner-entropy inequality, the extension to several modes and states with negative Wigner functions are outside this conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.covariancePP`
- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.covarianceXP`
- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.covarianceXX`
- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.densityEntropy`
- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.gaussianWigner`
- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.marginalP`
- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.marginalX`
- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.meanP`
- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.meanX`
- Truth anchor: `D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation.result`
- Dependency: [D5/S3/Entropy/Mixing/MixtureEntropyBracket](../../Entropy/Mixing/MixtureEntropyBracket.md)
- Dependency: [D5/S3/Fourier/Asymptotics/GaussianComplexMoments](../../Fourier/Asymptotics/GaussianComplexMoments.md)
