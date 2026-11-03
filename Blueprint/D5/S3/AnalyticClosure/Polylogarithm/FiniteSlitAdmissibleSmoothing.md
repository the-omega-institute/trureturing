# FiniteSlitAdmissibleSmoothing

## Abstract

The original admissible coefficients have every fixed positive smoothing sign and strict binomial excess.

**Theorem 1.1 (Every fixed smoothing order for admissible compositions).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitAdmissibleSmoothing.result`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitAdmissibleSmoothing.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

For every positive head greater than one, arbitrary positive-entry tail, positive ell and fixed j>=1, the original ordinary coefficients of (1-z)^(-j) times F(z)^(-ell) eventually are strictly positive and exceed zeta(head,tail)^(-ell) times choose(n+j-1,n). The existing ordinary inverse and endpoint results retain the strict-largest-index convention, removable origin and derivative divided by n factorial.

The first excess is exactly the first ordinary partial sum minus the actual endpoint. Its radial HasSum is proved by the public Cauchy product with the geometric series and subtraction of the endpoint geometric series. The quantitative admissible radial result discharges the positive margin. The generic signed-prefix Abel theorem then yields every fixed j while keeping the entire finite prefix.

This is the admissible branch of the original event. Leading head equal to one still requires its actual log-growth and normalized reciprocal radial margin. The full all-composition problem is not claimed solved; thresholds remain dependent on the fixed parameters.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitAdmissibleSmoothing.result`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinarySmoothing](FiniteSlitOrdinarySmoothing.md)
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitRadialMargin](FiniteSlitRadialMargin.md)
