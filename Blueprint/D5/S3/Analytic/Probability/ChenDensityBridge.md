# Density tilts and exact inclusion probabilities

## Abstract

Real density tilts on fixed-size samples preserve inclusion events up to the matched moment order.

**Definition 1.1 (Underlying measure of the uniform estimator law).**

$$\forall m : \mathbb{N}, \operatorname{uniformEstimatorLaw}\left(m\right) : \operatorname{Measure}\left(\mathbb{R}\right) = \left(\operatorname{map}\left(\operatorname{uniformSampleMeasure}\left(m\right), \operatorname{estimator}\left(m\right)\right) : \operatorname{Measure}\left(\mathbb{R}\right)\right)$$

*Formalization.* `D5/S3/Analytic/Probability/ChenDensityBridge.uniformEstimatorLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The estimator maps uniform samples of the prescribed size to real observations.

**Definition 1.2 (Tilted probability law on the same samples).**

$$\begin{aligned}\forall m : \mathbb{N}, \forall g : \mathbb{R} \to \mathbb{R}, \forall \left(hg : \operatorname{Measurable}\left(g\right)\right) \left(hn : \left(\forall x : \mathbb{R}, 0 \leq \operatorname{g}\left(x\right)\right)\right) \left(hm : \int \operatorname{g}\left(x\right) d\operatorname{uniformEstimatorLaw}\left(m\right) = 1\right),\\\operatorname{tiltedSample}\left(m, g, hg, hn, hm\right) : \operatorname{ProbabilityMeasure}\left(\operatorname{Sample}\left(m\right)\right),\\\left(\operatorname{tiltedSample}\left(m, g, hg, hn, hm\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right) = \operatorname{withDensity}\left(\left(\operatorname{uniformSampleMeasure}\left(m\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right), S \mapsto \operatorname{ENNReal.ofReal}\left(\operatorname{g}\left(\operatorname{estimator}\left(m, S\right)\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Analytic/Probability/ChenDensityBridge.tiltedSample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Normalization against the uniform estimator law makes this lifted measure a probability measure.

**Theorem 1.3 (Lifting a real density to the same finite sample space).**

$$\begin{aligned}\forall m,r : \mathbb{N}, \forall g : \mathbb{R} \to \mathbb{R}, \forall \left(hg : \operatorname{Measurable}\left(g\right)\right) \left(hn : \left(\forall x : \mathbb{R}, 0 \leq \operatorname{g}\left(x\right)\right)\right) \left(hm : \int \operatorname{g}\left(x\right) d\operatorname{uniformEstimatorLaw}\left(m\right) = 1\right),\\\left(\forall i : \mathbb{N}, 0 < i \Rightarrow i \leq r \Rightarrow \int x^{i} \left(\operatorname{g}\left(x\right)-1\right) d\operatorname{uniformEstimatorLaw}\left(m\right) = 0\right) \Rightarrow\\\left(\left(\operatorname{map}\left(\operatorname{tiltedSample}\left(m, g, hg, hn, hm\right), \operatorname{estimator}\left(m\right)\right) : \operatorname{Measure}\left(\mathbb{R}\right)\right) = \operatorname{withDensity}\left(\operatorname{uniformEstimatorLaw}\left(m\right), x \mapsto \operatorname{ENNReal.ofReal}\left(\operatorname{g}\left(x\right)\right)\right)\right) \land\\\left(\forall A : \operatorname{Finset}\left(\operatorname{Population}\left(m\right)\right), \operatorname{card}\left(A\right) \leq r \Rightarrow \left(\operatorname{tiltedSample}\left(m, g, hg, hn, hm\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right)\left(\operatorname{inclusion}\left(m, A\right)\right) = \left(\operatorname{uniformSampleMeasure}\left(m\right) : \operatorname{Measure}\left(\operatorname{Sample}\left(m\right)\right)\right)\left(\operatorname{inclusion}\left(m, A\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenDensityBridge.tiltedSample_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrating on a real event under the pushforward of the tilted sample law gives the same integral as tilting the uniform estimator law by g.

For a prescribed subset A, the finite sampling identity converts the restricted integral of the centered density into an integral against an inclusion polynomial of degree at most the cardinality of A. Normalization handles the constant coefficient. The centered moment equations handle every other coefficient. The resulting equality of event masses holds in ENNReal.

## References

- Truth anchor: `D5/S3/Analytic/Probability/ChenDensityBridge.tiltedSample`
- Truth anchor: `D5/S3/Analytic/Probability/ChenDensityBridge.tiltedSample_spec`
- Truth anchor: `D5/S3/Analytic/Probability/ChenDensityBridge.uniformEstimatorLaw`
- Dependency: [D5/S3/Analytic/Probability/ChenFixedOrderSampling](ChenFixedOrderSampling.md)
