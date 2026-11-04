# FiniteSlitOrdinaryCoefficients

## Abstract

The original ordinary formal inverse has exactly the Taylor coefficients of the actual normalized composition reciprocal.

**Theorem 1.1 (Exact ordinary coefficients for every positive composition).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryCoefficients.result`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryCoefficients.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

Let phi be PowerSeries.mk of CompositionDisk.coefficient head tail over the real field. ordinary is exactly the formal inverse of phi to the positive integer power ell. Every natural coefficient, cast to complex, equals iteratedDeriv n of FiniteSlitCompositionMoments.reciprocal at zero divided by n factorial. All positive heads and ell, every positive-entry tail including the empty tail, and n=0 are included.

The proof uses the existing actual analytic coefficient identity, reality and disk HasSum from FiniteSlitCoefficientIdentity.result. The Cauchy product of scalar sums agrees with ordinary formal multiplication. Scalar analytic uniqueness identifies the product of the actual Taylor series and phi to power ell with one. The positive source constant makes this inverse unique; the real-to-complex coefficient map preserves the product. No replacement analytic function or assumed coefficient-identification premise is introduced.

The exact coefficients therefore have HasSum equal to the actual reciprocal throughout the open unit disk. The same actual outer circle and upper-bank moment prove an eventually strictly negative ordinary coefficient for every composition and ell. This is the j=0 clause of the Xu--Zhao target.

The complete original target also requires eventual positivity for every fixed integer j>=1 and, for admissible head>1, strict excess over the binomial coefficient divided by the corresponding multiple zeta value to power ell. Absolute summability, the total endpoint sum, and the signed finite prefixes in successive sums remain separate obligations. This result alone does not resolve the full external problem.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryCoefficients.result`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCoefficientIdentity](FiniteSlitCoefficientIdentity.md)
