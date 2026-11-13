# Bounded variation correlation summation

## Abstract

Uniform partial-sum discrepancy controls weighted sums with bounded variation weights.

**Theorem 1.1 (BV discrepancy against an integrable density).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation.bv_discrepancy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation.bv_discrepancy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On an interval (a,b] with natural endpoints, suppose the discrepancy between the atomic prefix sum of c and the integral of an integrable real density is bounded by E at every real cut. A globally bounded variation weight with absolute value at most U on [a,b] and total variation at most V has weighted discrepancy at most E(U+V). No sign condition on the density or continuity convention on the weight is imposed. Finite step approximations preserve every sampled integer value; their variations are bounded by the weight's variation, and dominated convergence gives the density integral.

**Theorem 1.2 (Dyadic BV correlation discrepancy).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation.bv_correlation_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation.bv_correlation_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real N≥2, a bound E on the discrepancy between the sum of f over N<n≤y and c(y−N), uniform for N≤y≤2N, gives a weighted discrepancy bound E times the sum of U and the variation of v on [N,2N]. Here U bounds the absolute value of v on that interval. The comparison integral is c times the integral of v from N to 2N. The endpoints may be nonintegral and the weight may take arbitrary values at integer atoms. Clamping the weight to the dyadic interval preserves the variation bound.

**Theorem 1.3 (Polynomial logarithmic weights).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation.polynomial_log_bv_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation.polynomial_log_bv_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real polynomial p there is a nonnegative constant C depending only on p. For N≥2, if a global BV weight w has absolute value bounded by U and total variation bounded by V, then x↦w(x/N)p(log x) has bounded variation on [N,2N]. Its supremum bound K plus its variation is at most C(U+V)(1+log N) to the natural degree of p. Polynomial evaluation and Lipschitz bounds on [0,1+log N], the monotonicity of log, and the variation bound for a product give this estimate. Thus the same conclusion with CB holds whenever U+V≤B.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation.bv_correlation_discrepancy`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation.bv_discrepancy_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BVCorrelationSummation.polynomial_log_bv_bound`
