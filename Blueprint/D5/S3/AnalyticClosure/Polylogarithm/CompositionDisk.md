# CompositionDisk

## Abstract

Strict nested coefficients give the actual depth-normalized analytic series on the unit disk.

**Theorem 1.1 (Bounds, vanishing and the minimal strict tuple).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk.source_coefficient_control`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk.source_coefficient_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

For every positive composition ks and bound N, the recursive strict sum H is nonnegative and at most N to the length of ks. It vanishes below that length and is strictly positive at and above it. At the first nonzero index it equals the reciprocal product along the unique minimal tuple (length,...,1). Structural induction proves the bound and the positive surviving summand; the bounds are used in the actual infinite-series estimates.

**Theorem 1.2 (Absolute convergence and exact source realization).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk.source_series`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk.source_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

For every positive head and tail, the coefficients H(tail,n+d-1)/(n+d)^head are strictly positive. Their scalar series F is absolutely convergent and analytic at every point of the open unit disk. Its value at zero is the positive minimal-tuple product. The function z^d F equals both the recursive source sum and the independent sum over strict nested indices, and has analytic order exactly d at zero. Polynomial-weighted geometric estimates supply the live convergence premise of the frozen scalar-series supplier. This source normalization is part of the disk consumer; it asserts no boundary multiple-zeta convergence or coefficient-sign conjecture.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk.source_coefficient_control`
- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk.source_series`
- Dependency: [D5/S3/Weil/Probability/AnalyticLogarithmicContinuation](../../Weil/Probability/AnalyticLogarithmicContinuation.md)
