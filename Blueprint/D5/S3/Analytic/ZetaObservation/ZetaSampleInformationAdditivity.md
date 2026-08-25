# Zeta Sample Information Additivity

## Abstract

Independent zeta observations add their Fisher information exactly.

**Theorem 1.1 (Independent zeta samples have additive information).**

$$1 < s \Rightarrow \operatorname{VarianceUnder}\left(\operatorname{ProductZetaLaw}\left(s, m\right), \operatorname{SumOfLogCoordinates}\left(m\right)\right) = \operatorname{Product}\left(m, \operatorname{VarianceUnder}\left(\operatorname{ZetaLaw}\left(s\right), \operatorname{LogObservation}\left(\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/ZetaSampleInformationAdditivity.zeta_sample_information_additive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-sample Fisher information is represented by the variance of the logarithmic observation under the zeta law. The m-sample quantity is the variance of the sum of the m coordinate observations under the canonical product zeta measure.

Above inverse temperature one, the logarithmic observation has a finite second moment. Variance additivity for the independent product coordinates then makes the joint information exactly m times the one-sample information, including the zero-sample case.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/ZetaSampleInformationAdditivity.zeta_sample_information_additive`
