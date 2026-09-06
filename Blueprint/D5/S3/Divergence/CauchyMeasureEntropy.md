# Cauchy Measure Relative Entropy

## Abstract

The relative entropy of positive-scale Cauchy measures at a common center has its closed form and obeys strict scale-flow laws.

**Theorem 1.1 (Cauchy measure relative entropy and its analytic prerequisites).**

$$\forall gamma \in \mathbb{R}, a \in NNReal, b \in NNReal,\; \left(a \ne 0 \land b \ne 0\right) \Rightarrow \left(\operatorname{AbsolutelyContinuous}\left(\operatorname{cauchyMeasure}\left(gamma, a\right), \operatorname{cauchyMeasure}\left(gamma, b\right)\right) \land \left(\operatorname{Integrable}\left(\operatorname{llr}\left(\operatorname{cauchyMeasure}\left(gamma, a\right), \operatorname{cauchyMeasure}\left(gamma, b\right)\right), \operatorname{cauchyMeasure}\left(gamma, a\right)\right) \land \operatorname{klDiv}\left(\operatorname{cauchyMeasure}\left(gamma, a\right), \operatorname{cauchyMeasure}\left(gamma, b\right)\right) = \operatorname{ofReal}\left(\operatorname{cauchyKL}\left(gamma, \operatorname{toReal}\left(a\right), gamma, \operatorname{toReal}\left(b\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CauchyMeasureEntropy.cauchy_measure_relative_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NNReal denotes the nonnegative real numbers. Both scales are nonzero. The measures, log-likelihood ratio llr, and ENNReal-valued klDiv are Mathlib's existing objects. cauchyKL is the imported real closed form, with nonnegative scales coerced to real numbers.

Positive densities establish absolute continuity and identify the Radon--Nikodym density ratio. A uniform bound on that ratio and its reciprocal proves logarithmic integrability. Differentiation under the integral, a mixed rational-kernel evaluation, and the mean value theorem compute the logarithmic expectation.

**Theorem 1.2 (Positive smoothing, admissible reverse shifts, and boundary divergence).**

$$\forall gamma \in \mathbb{R}, delta \in \mathbb{R}, omega \in \mathbb{R},\; \left(0 < omega \land omega < delta\right) \Rightarrow \left(\left(\forall h \in \mathbb{R},\; 0 < h \Rightarrow \operatorname{klDiv}\left(\operatorname{cauchyMeasure}\left(gamma, \operatorname{toNNReal}\left(delta + h - omega\right)\right), \operatorname{cauchyMeasure}\left(gamma, \operatorname{toNNReal}\left(delta + h + omega\right)\right)\right) < \operatorname{klDiv}\left(\operatorname{cauchyMeasure}\left(gamma, \operatorname{toNNReal}\left(delta - omega\right)\right), \operatorname{cauchyMeasure}\left(gamma, \operatorname{toNNReal}\left(delta + omega\right)\right)\right)\right) \land \left(\left(\forall h \in \mathbb{R},\; \left(h < 0 \land omega < delta + h\right) \Rightarrow \operatorname{klDiv}\left(\operatorname{cauchyMeasure}\left(gamma, \operatorname{toNNReal}\left(delta - omega\right)\right), \operatorname{cauchyMeasure}\left(gamma, \operatorname{toNNReal}\left(delta + omega\right)\right)\right) < \operatorname{klDiv}\left(\operatorname{cauchyMeasure}\left(gamma, \operatorname{toNNReal}\left(delta + h - omega\right)\right), \operatorname{cauchyMeasure}\left(gamma, \operatorname{toNNReal}\left(delta + h + omega\right)\right)\right)\right) \land \operatorname{Tendsto}\left((w \in \mathbb{R} \mapsto \operatorname{klDiv}\left(\operatorname{cauchyMeasure}\left(gamma, \operatorname{toNNReal}\left(delta - w\right)\right), \operatorname{cauchyMeasure}\left(gamma, \operatorname{toNNReal}\left(delta + w\right)\right)\right)), \operatorname{nhdsLT}\left(delta\right), \operatorname{nhds}\left(\infty\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/CauchyMeasureEntropy.cauchy_poisson_coarse_graining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common time shift h replaces the two scales delta minus omega and delta plus omega by delta plus h minus omega and delta plus h plus omega. The source domain is zero less than omega less than delta. A negative shift must also preserve omega less than delta plus h, so both scales remain positive.

toNNReal is the canonical real-to-nonnegative-real conversion; every scale in the strict inequalities is positive. nhdsLT(delta) is the left neighborhood filter. The final conjunct is a limit in ENNReal to infinity, with the real variable w explicitly bound. It does not substitute the zero-scale Dirac branch into the positive-scale evaluation.

## References

- Truth anchor: `D5/S3/Divergence/CauchyMeasureEntropy.cauchy_measure_relative_entropy`
- Truth anchor: `D5/S3/Divergence/CauchyMeasureEntropy.cauchy_poisson_coarse_graining`
- Dependency: [D5/S3/Divergence/CauchyClosedForm](CauchyClosedForm.md)
