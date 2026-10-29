# CompositionReciprocalSeries

## Abstract

The real ordinary formal inverse represents the actual normalized analytic reciprocal.

**Definition 1.1 (The ordinary formal inverse).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries.ordinarySeries`

*Formalization.* `D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries.ordinarySeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

For head : PNat, tail : List PNat and ell : PNat, ordinarySeries is the inverse of the ell-th power of PowerSeries.mk applied to the actual CompositionDisk.coefficient head tail. The composition is head :: tail; tail may be empty and may contain any finite block of leading ones.

**Definition 1.2 (Ordinary real coefficients).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries.ordinaryCoefficient`

*Formalization.* `D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries.ordinaryCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

ordinaryCoefficient is the n-th real PowerSeries coefficient of ordinarySeries. It uses ordinary powers z^n, with no exponential-generating factorial.

**Definition 1.3 (The actual analytic reciprocal).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries.reciprocal`

*Formalization.* `D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries.reciprocal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

reciprocal inverts the ell-th power of CompositionZeroFreeCollar.normalizedContinuation. That continuation removes the source zero of order CompositionDisk.depth tail at the origin. The local scalar power series of reciprocal has exactly the complex casts of ordinaryCoefficient: the Cauchy product with the source series power equals one, and uniqueness identifies its coefficients with the real formal inverse. Its n-th coefficient is the Cauchy integral on the circle of radius one half, divided by 2 pi i.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries.ordinaryCoefficient`
- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries.ordinarySeries`
- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries.reciprocal`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFreeCollar](CompositionZeroFreeCollar.md)
