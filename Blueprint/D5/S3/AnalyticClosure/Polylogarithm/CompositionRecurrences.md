# CompositionRecurrences

## Abstract

The actual strict source series satisfies both differential recurrences, including at zero.

**Theorem 1.1 (Termwise derivative of the strict source sum).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences.source_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences.source_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

At each point in the unit disk, choose a larger radius still below one. The source-specific coefficient bound gives a summable common majorant for the differentiated terms on that disk. The derivative is the actual series with the head exponent decreased by one; exponent zero is included. The termwise differentiation theorem is applied directly from Mathlib.

**Theorem 1.2 (Both recurrences with the correct removable values).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences.source_recurrences`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences.source_recurrences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

For leading one, the derivative equals source(tail)/(1-z) throughout the disk, with source(empty)=1. The strict finite-sum difference telescopes only after summability of the shifted series has been proved. For head greater than one, the derivative equals source(head-1,tail)/z away from zero; at zero it is one for an empty tail and zero otherwise. Total division by zero is never used as that removable value. These identities are premises proved within the source unit, not hypotheses of its all-composition disk consumer.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences.source_derivative`
- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences.source_recurrences`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk](CompositionDisk.md)
