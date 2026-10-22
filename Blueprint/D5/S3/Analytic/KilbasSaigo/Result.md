# The two-sided estimate

## Abstract

Hyperbolic bounds for the Kilbas-Saigo function on the negative half-line.

**Theorem 1.1 (The full parameter range).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Result.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real alpha,m,l,x with 0<alpha<=1, m>0, l>m-1/alpha and x>=0, E(alpha,m,l)(-x) is bounded below by 1/(1+Gamma(1+alpha(l-m)) x/Gamma(1+alpha(l-m+1))) and above by 1/(1+Gamma(1+alpha l) x/Gamma(1+alpha(1+l))). The defining series and its derivatives converge on the entire real line. Positive Gamma increment kernels establish the fractional range; affine differential equations establish alpha=1. Strict positivity, decreasingness and convexity give the two estimates.

## References

- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Result.result`
- Dependency: [D5/S3/Analytic/KilbasSaigo/Bounds](Bounds.md)
