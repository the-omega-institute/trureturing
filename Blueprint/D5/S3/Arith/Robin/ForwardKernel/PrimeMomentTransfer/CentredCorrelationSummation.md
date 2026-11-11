# Centred weighted tuple correlations

## Abstract

Mean-square prime correlations control polynomial logarithmic BV sums after aggregation over shift tuples.

Assume MeanSquareHL(q,SS,beta) and SS(empty)=1. The mean-square hypothesis bounds the sum of squared raw correlation errors over all ordered injective r-tuples in [1,K], for 1<=r<=q, by C N^(1+2 epsilon) K^r. Its constant and threshold are uniform in r, natural 1<=K<=M N^beta, and real N<=y<=2N, after epsilon>0 and M>=1 have been fixed. The centred singular series is the alternating subset transform of SS.

Chan, A note on primes in short intervals, International Journal of Number Theory 2 (2006), 105–110, supplies the single-interval precedent for replacing pointwise correlation errors by mean-square errors. The interval-box aggregation, overlapping mixed moments and BV polynomial logarithmic weights here are repo-derived. Cauchy–Schwarz bounds total raw errors; the tuple-subset multiplicity estimate accounts for the unused shifts. The commutative-ring centred product expansion then controls the total centred error.

**Theorem 1.1 (Polynomial logarithmic weights on aggregated correlations).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation.centred_polynomial_log_correlation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation.centred_polynomial_log_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For M>=1, epsilon>0 and a real polynomial p there are C>=0 and a threshold such that every subsequent real N satisfies N>=2 and the following bound. Choose any natural k<=q and natural 1<=K<=M N^beta, any subfamily T of the full box of k-tuples with entries in [1,K], and any assignment Q(d,J) of coefficient polynomials to a tuple d and a subset J of its distinct values. Aggregate the centred products over all d in T and J contained in image(d) for which Q(d,J)=p. The weighted dyadic sum of this aggregate with weight w(n/N) p(log n), minus the corresponding sum of centred singular series times the integral of w(x/N) p(log x), has absolute value at most C B N^(1/2+epsilon) K^k (1+log N)^natDegree(p). The constant may depend on q, SS, beta, M, epsilon and p. The bound holds for every supported BV weight w with BVBound(w,B), uniformly in k, K, T, Q, B and w.

The tuple and subset sums are taken before BV partial summation, so no sum of separate suprema over cutoffs is needed. Subtracting the aggregate raw-cut error at N from the aggregate error at y gives every dyadic partial sum required by the BV discrepancy theorem. Both cutoffs lie in [N,2N]; the mean-square hypothesis is never used outside that interval. The empty subset contributes only the floor discrepancy and is controlled using SS(empty)=1. Weights may jump at integer sampling points.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredCorrelationSummation.centred_polynomial_log_correlation`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation](BVCorrelationSummation.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CentredProductExpansion](CentredProductExpansion.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MeanSquareCorrelation](MeanSquareCorrelation.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/TupleSubsetMultiplicity](TupleSubsetMultiplicity.md)
