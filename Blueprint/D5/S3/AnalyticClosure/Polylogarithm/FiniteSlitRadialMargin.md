# FiniteSlitRadialMargin

## Abstract

A positive radial margin for admissible compositions

**Theorem 1.1 (A positive radial margin for admissible compositions).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitRadialMargin.result`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitRadialMargin.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

For every positive head greater than one, every positive-entry tail and positive reciprocal power, the actual normalized reciprocal has a uniform strictly positive radial quotient (A(r)-endpoint)/(1-r) near one. CompositionBoundary supplies the positive total Z of the original source coefficients, and CompositionDisk supplies strict positivity of the coefficient f(1).

For 0<r<1 the positive source series has value x with 0<x<=Z. Its exact difference from Z is at least f(1)(1-r). Comparing inverse powers gives the lower bound f(1)/Z^2 times Z^(-k), where ell=k+1. Source agreement with the normalized continuation identifies this real estimate with the actual reciprocal, preserving the removable origin and ordinary normalization.

This result covers the admissible branch only. No logarithmic growth estimate or radial margin for a leading head equal to one is claimed here; the complete original event retains that obligation.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitRadialMargin.result`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryEndpoint](FiniteSlitOrdinaryEndpoint.md)
