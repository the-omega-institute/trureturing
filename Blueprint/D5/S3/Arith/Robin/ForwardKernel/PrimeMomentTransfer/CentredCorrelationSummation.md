# Centred weighted correlations

## Abstract

Centred prime correlations satisfy uniform polynomial logarithmic BV weights.

Assume the strong Hardy–Littlewood correlation estimate for up to four distinct positive shifts and an abstract singular series whose empty value is one. The centred singular series is its alternating subset transform. Weights may jump at integer sampling points.

**Theorem 1.1 (Polynomial logarithmic weights).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation.centred_polynomial_log_correlation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation.centred_polynomial_log_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a real polynomial p. The sum over N less than n at most 2N of w(n/N) p(log n) times the centred product for D differs from the centred singular series times the integral of w(x/N) p(log x) by at most C B N to the power one half plus epsilon times (1+log N) to the degree of p. The constant is chosen before D and before any compactly supported BV weight whose supremum bound plus variation is at most B. Subtracting two real-cut partial sums supplies the dyadic discrepancy; finite BV summation controls the weight without a continuity assumption.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation.centred_polynomial_log_correlation`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation](BVCorrelationSummation.md)
