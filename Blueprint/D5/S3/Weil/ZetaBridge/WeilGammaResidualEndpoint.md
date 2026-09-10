# Gamma Residual Endpoint

## Abstract

The actual Gamma endpoint logarithm admits a complete squared-tail bound, with integrability proved before use in a physical residual certificate.

**Theorem 1.1 (Actual singular logarithm and local endpoint distance).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint.gamma_endpoint_log_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint.gamma_endpoint_log_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<t<=1 and d>=t, prove |log(1-exp(-d))|<=1-log(t). The exponential tangent inequality gives t*exp(-t)<=1-exp(-t); positivity and logarithm monotonicity prove the bound. The singular coefficient is not suppressed and no finite endpoint value is substituted.

**Theorem 1.2 (Complete square-envelope integral).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint.exponential_affine_square_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint.exponential_affine_square_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real A,B,T, prove both integrability on (T,infinity) and the exact integral of exp(-x)*(A+B*x)^2. An explicit differentiated primitive and the existing polynomial-times-exponential decay give the improper integral. All mixed terms and the infinite integration range remain present.

**Theorem 1.3 (Actual endpoint expression has a certified finite squared mass).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint.gamma_logarithmic_endpoint_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint.gamma_logarithmic_endpoint_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f,g be measurable complex coefficient functions and distance a measurable real function. On x>T>=0 assume norms of f and g bounded by nonnegative A,B and distance(x)>=exp(-x). For the actual expression R=f+log(1-exp(-distance))*g, prove integrability of exp(-x)*norm(R)^2 and its explicit full tail upper bound. The preceding singular logarithm estimate is substituted before the square and all cross terms are retained.

The executable consumer evaluates the entire same-window Gamma, Sp, prime, pole and fixed-Rayleigh residual of the genuine prolate model. It uses dyadic endpoint strips, these logarithmic envelopes, and directed Taylor integration with a complex-disc Cauchy remainder. The physical t=exp(-x) substitution, original Gamma realization and piecewise-C1 graph-error bound remain separately documented paper bridges. Lean elaboration, transitive axiom checking and Scribe emission were not executed. The source does not prove a small residual/gap or an all-scale Xi limit.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint.exponential_affine_square_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint.gamma_endpoint_log_bound`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGammaResidualEndpoint.gamma_logarithmic_endpoint_tail`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilGammaLogarithmicSeed](WeilGammaLogarithmicSeed.md)
