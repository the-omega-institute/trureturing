# The two-sided estimate

## Abstract

Hyperbolic bounds for the Kilbas-Saigo function on the negative half-line.

**Theorem 1.1 (The full parameter range).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/boudabsa-simon-2021-kilbas-saigo-hyperbolic-bounds` (proved) by `D5/S3/Analytic/KilbasSaigo/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"boudabsa-simon-2021-kilbas-saigo-hyperbolic-bounds","declaration_gid":"D5/S3/Analytic/KilbasSaigo/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* L. Boudabsa and T. Simon (2021). *Some properties of the Kilbas–Saigo function*. DOI: [10.3390/math9030217](https://doi.org/10.3390/math9030217). URL: <https://arxiv.org/abs/2012.05666>.

*Commentary.*

For every real alpha,m,l,x with 0<alpha<=1, m>0, l>m-1/alpha and x>=0, E(alpha,m,l)(-x) is bounded below by 1/(1+Gamma(1+alpha(l-m)) x/Gamma(1+alpha(l-m+1))) and above by 1/(1+Gamma(1+alpha l) x/Gamma(1+alpha(1+l))). The defining series and its derivatives converge on the entire real line. Positive Gamma increment kernels establish the fractional range; affine differential equations establish alpha=1. Strict positivity, decreasingness and convexity give the two estimates.

## References

- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Result.result`
- Dependency: [D5/S3/Analytic/KilbasSaigo/Bounds](Bounds.md)
