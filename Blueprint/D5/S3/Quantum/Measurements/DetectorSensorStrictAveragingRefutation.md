# Strict averaging fails for optimal detector-sensor probes

## Abstract

Two optimal three-sensor probes refute strict improvement by coefficient-square averaging.

**Definition 1.1 (Optimal discrimination success).**

$$\forall (n: \mathbb{N}), (\forall (\theta: \mathbb{R}), (\forall (\psi: (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{C}), ((\operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.optSuccess}\left(\theta, \psi\right): \mathbb{R}) = \operatorname{iSup}\left(\lambda (M: \operatorname{D5.S3.Quantum.Entanglement.TriangleIndependentSourceNoise.LocalPOVM}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Bool}, \operatorname{Fin}\left(n\right)\right)) \mapsto (\operatorname{D5.S3.Quantum.Measurement.DetectorSensorDickeOptimality.isoSuccess}\left(\theta, \psi, M\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.optSuccess` (`✓ std3`).

*Citation.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

The supremum of the equal-prior discrimination success `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.isoSuccess` ranges over every global measurement of type `D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise.LocalPOVM` with outcomes Fin n. The possible final states are given by `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.fire`. This is the success counterpart of the minimum-error objective P: problem-related.tex, lines 23–47, and searching.tex, lines 93–105. The definition permits every natural n and every amplitude function; normalization is imposed in the conjecture.

**Definition 1.2 (Minimum error objective).**

$$\forall (n: \mathbb{N}), (\forall (\theta: \mathbb{R}), (\forall (\psi: (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{C}), ((\operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.errorProb}\left(\theta, \psi\right): \mathbb{R}) = (1: \mathbb{R}) - \operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.optSuccess}\left(\theta, \psi\right))))$$

*Formalization.* `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.errorProb` (`✓ std3`).

*Citation.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

The error objective is one minus optimal success. For a normalized probe this encodes P in problem-related.tex, lines 35–47; searching.tex, lines 100–105, writes the error as one minus the success of an optimal POVM. The formula itself is defined without a normalization hypothesis.

**Definition 1.3 (Coefficient-square average).**

$$\forall (n: \mathbb{N}), (\forall (\psi: (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{C}), (\forall (\psi': (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{C}), ((\operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.average}\left(\psi, \psi'\right): (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{C}) = \lambda (x: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \mapsto (\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\frac{\operatorname{Complex.normSq}\left(\psi\left(x\right)\right) + \operatorname{Complex.normSq}\left(\psi'\left(x\right)\right)}{(2: \mathbb{R})}\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.average` (`✓ std3`).

*Citation.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

At each Boolean word x, average takes the nonnegative real square root of the mean of the two squared complex amplitudes, then includes that real number in the complex scalars. This is the state in optimal.tex, line 144. It averages coefficient-squares and assigns nonnegative real amplitudes; it does not retain the phases of the two inputs.

**Definition 1.4 (The strict-averaging conjecture).**

$$\operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.claim} \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (\theta: \mathbb{R}), (((0: \mathbb{R}) < \theta) \to ((\theta < \operatorname{Real.pi}) \to (\forall (\psi: (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{C}), (\forall (\psi': (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{C}), ((\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}} (\operatorname{Complex.normSq}\left(\psi\left(x\right)\right)) = (1: \mathbb{R})) \to ((\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}} (\operatorname{Complex.normSq}\left(\psi'\left(x\right)\right)) = (1: \mathbb{R})) \to ((\exists (x: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}), (\operatorname{Complex.normSq}\left(\psi\left(x\right)\right) \ne \operatorname{Complex.normSq}\left(\psi'\left(x\right)\right))) \to ((\operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.errorProb}\left(\theta, \psi\right) = \operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.errorProb}\left(\theta, \psi'\right)) \to (\operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.errorProb}\left(\theta, \operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.average}\left(\psi, \psi'\right)\right) < \operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.errorProb}\left(\theta, \psi'\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.claim` (`✓ std3`).

*Citation.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

Conjecture 2, optimal.tex, lines 131–149, asserts that two normalized probes with unequal coefficient-squares somewhere and equal minimum error have an average with strictly smaller error. The unitary has eigenvalues exp(±iθ). Its angle range in problem-related.tex, lines 17–21, is expressed here in radians as 0 < θ < π. The statement quantifies over every natural sensor count n, every such angle θ, and every pair ψ, ψ′ of normalized complex amplitude functions on Fin n → Bool.

**Theorem 1.5 (Two distinct optimal probes prevent strict improvement).**

$$\neg (\forall (n: \mathbb{N}), (\forall (\theta: \mathbb{R}), (((0: \mathbb{R}) < \theta) \to ((\theta < \operatorname{Real.pi}) \to (\forall (\psi: (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{C}), (\forall (\psi': (\operatorname{Fin}\left(n\right) \to \operatorname{Bool}) \to \mathbb{C}), ((\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}} (\operatorname{Complex.normSq}\left(\psi\left(x\right)\right)) = (1: \mathbb{R})) \to ((\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}} (\operatorname{Complex.normSq}\left(\psi'\left(x\right)\right)) = (1: \mathbb{R})) \to ((\exists (x: \operatorname{Fin}\left(n\right) \to \operatorname{Bool}), (\operatorname{Complex.normSq}\left(\psi\left(x\right)\right) \ne \operatorname{Complex.normSq}\left(\psi'\left(x\right)\right))) \to ((\operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.errorProb}\left(\theta, \psi\right) = \operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.errorProb}\left(\theta, \psi'\right)) \to (\operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.errorProb}\left(\theta, \operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.average}\left(\psi, \psi'\right)\right) < \operatorname{D5.S3.Quantum.Measurements.DetectorSensorStrictAveragingRefutation.errorProb}\left(\theta, \psi'\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhan-gupta-hillery-2024-detector-sensor-strict-averaging-refutation` (refuted) by `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhan-gupta-hillery-2024-detector-sensor-strict-averaging-refutation","declaration_gid":"D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. Zhan, H. Gupta, M. Hillery (2024). *Optimizing Initial State of Detector Sensors in Quantum Sensor Networks*. DOI: [10.1145/3655028](https://doi.org/10.1145/3655028). URL: <https://arxiv.org/abs/2306.17401v6>.

*Commentary.*

For three sensors, take φ₁ and φ₂ to have amplitude 1/√3 on the words of weight one and two, respectively, and amplitude zero elsewhere. More generally, the uniform weight-l probe has squared amplitude 1/(Nat.choose 3 l) on that weight class and zero outside it. This follows by squaring its real inverse square-root amplitude. The threshold T(3) is π/3: arccos(1/2) = π/3 and arccos(−1/2) = π − arccos(1/2). Thus θ = π/4 is positive and at most T(3).

For the selected sensor positions 0 and 1, the agreement counts at weights 0, 1, 2, 3 are all one, and the disagreement counts are 0, 2, 2, 0. The disagreement counting identity and the partition of each weight class give these values. Since cos(2θ) = 0, the overlap ratios are 1, 1/3, 1/3, 1. Both weights one and two therefore minimize the ratio. At the word whose only true coordinate is 0, the squared amplitudes of φ₁ and φ₂ are 1/3 and zero, so they differ.

There is a three-outcome POVM with identity effect at outcome 0 and zero effects at the other outcomes.

For any normalized probe, `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.global_success_upper_bound` at n = 3 and θ = π/4 bounds every POVM success by d 3 (cstar 3 (π/4))². This bounds the range above without evaluating the bound.

The `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.result` applies to each minimizing weight. For every normalized competitor ψ and every POVM M it supplies a POVM M′ on φ₁, and likewise on φ₂, whose success is at least that of ψ with M. The weight-class normalization theorem gives unit norm for both proposed probes. The nonempty POVM type and the upper bounds on success allow this comparison to pass to suprema: every normalized competitor has optimal success at most that of either φ₁ or φ₂.

The average of any two normalized probes is normalized: its squared amplitude at x is exactly the mean of their squared amplitudes, because that mean is nonnegative; summing gives (1 + 1)/2 = 1. Applying the two optimal-success comparisons to φ₁ and φ₂ in both directions gives equal optimal successes and hence equal errors. Applying the comparison for φ₂ to their normalized average shows that the average has success at most that of φ₂, and thus error at least that of φ₂.

Finally, π/4 < π, both probes are normalized, their coefficient-squares differ, and their errors agree. The conjecture would give an average error strictly smaller than the error of φ₂, contradicting the opposite weak inequality. This refutes the quantified strict-averaging statement.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/TriangleIndependentSourceNoise.LocalPOVM`
- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.fire`
- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.global_success_upper_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.isoSuccess`
- Truth anchor: `D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality.result`
- Truth anchor: `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.average`
- Truth anchor: `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.errorProb`
- Truth anchor: `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.optSuccess`
- Truth anchor: `D5/S3/Quantum/Measurements/DetectorSensorStrictAveragingRefutation.result`
- Dependency: [D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance](../Measurement/AnticoherenceSpinCovariance.md)
- Dependency: [D5/S3/Quantum/Measurement/DetectorSensorDickeOptimality](../Measurement/DetectorSensorDickeOptimality.md)
