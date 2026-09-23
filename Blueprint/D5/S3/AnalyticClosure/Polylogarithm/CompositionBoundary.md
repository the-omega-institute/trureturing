# CompositionBoundary

## Abstract

Every admissible positive composition has a positive strict multiple-zeta total, equal to the boundary value of its actual normalized source series.

**Theorem 1.1 (Unbounded summability and the radial multiple-zeta value).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionBoundary.result`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/CompositionBoundary.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

The head is any positive integer greater than one, and the tail is any finite list of positive integers, including the empty list. The frozen coefficients are summable. Independently, the full family over strict decreasing positive tuples is summable: Indices chooses the largest entry n+1 and then uses the frozen StrictIndices below n+1. The reciprocal weight puts the head exponent on that largest entry. Its total zeta equals the coefficient sum and is strictly positive.

Structural induction bounds the actual nested harmonic sum by the ordinary harmonic number raised to the tail length. Mathlib's harmonic logarithm bound and positive-power domination of logarithms give an eventual constant multiple of the p-series with exponent three halves. The finite strict-index sums identify the full dependent-sum family; the initial terms below the tail length vanish exactly. Positivity uses the frozen positive coefficient at index zero after summability has been proved.

The theorem explicitly identifies the frozen normalized series with the source divided by its depth power at every nonzero point in the unit disk. Tannery's dominated-series theorem then proves that this same normalized function tends to the positive zeta total as real r approaches one from below. No summability, source equivalence, positivity or radial-limit assumption is supplied.

This is the preregistered W03 intermediate bridge. The one exported theorem has source-specific nested-sum and unbounded convergence content; classical analytic suppliers remain applications inside its proof. No separate convenience theorem is exported. This result settles no coefficient-sign conjecture, asserts no bank asymptotic or slit-plane extension, and earns zero solved-problem credit.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionBoundary.result`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk](CompositionDisk.md)
