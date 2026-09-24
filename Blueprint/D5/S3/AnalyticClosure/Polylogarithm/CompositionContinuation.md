# CompositionContinuation

## Abstract

Recursive segment integrals define the positive-composition slit branches.

**Definition 1.1 (Attributed segment integral).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionContinuation.starPrimitive`

*Formalization.* `D5/S3/AnalyticClosure/Polylogarithm/CompositionContinuation.starPrimitive` (`✓ std3`).

*Citation.* Will (Ziang) Li (2026). *Primitives of Holomorphic Functions on Star-Shaped Domains*. URL: <https://github.com/will1491/RiemannDynamics/blob/b3fa37cc0f18a23ea66b654ea3f73eb472129010/RiemannDynamics/Hyperbolic/PlaneGeometry/StarShapedPrimitive.lean>.

*Commentary.*

The segment integral from p to z is copied from Will (Ziang) Li's immutable RiemannDynamics core. The Lean module retains the exact upstream LICENSE, copyright, attribution, extraction notice and own-pinned-Mathlib retirement condition. Its primitive proof remains local in the actual source consumer.

**Definition 1.2 (The actual continued family).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionContinuation.continued`

*Formalization.* `D5/S3/AnalyticClosure/Polylogarithm/CompositionContinuation.continued` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Acknowledgement.* Will (Ziang) Li (2026). *Primitives of Holomorphic Functions on Star-Shaped Domains*. URL: <https://github.com/will1491/RiemannDynamics/blob/b3fa37cc0f18a23ea66b654ea3f73eb472129010/RiemannDynamics/Hyperbolic/PlaneGeometry/StarShapedPrimitive.lean>.

*Commentary.*

omega is the full set of complex z with 1-z in Complex.slitPlane. The empty composition is the constant one. For a nonempty composition, raise first integrates the tail branch divided by 1-z, then integrates dslope repeatedly to raise the leading exponent. dslope uses the derivative at zero. These definitions assume neither source continuation nor a recurrence or convergence assertion outside the disk.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionContinuation.continued`
- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionContinuation.starPrimitive`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences](CompositionRecurrences.md)
