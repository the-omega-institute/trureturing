# One small coordinate

## Abstract

A family of strict Gini comparison reversals on the positive half-line.

**Theorem 1.1 (Factorization of the comparison numerator).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Witness.witness_identity`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GiniStationaryTest/Witness.witness_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

For all real t and k, (t+k)^3(1+kt) - (k+1)^3 t(t^2+k) equals k(t-1)^3(t-k^2). The identity is polynomial and has no positivity assumptions.

**Theorem 1.2 (Power sum of the comparison tuple).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Witness.sum_highTuple_rpow`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GiniStationaryTest/Witness.sum_highTuple_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

For every natural m and real t and p, the sum of the p-th powers of the tuple (t,1,...,1) with m+1 coordinates is t^p+m. Splitting off the first coordinate gives the formula used at exponents 1, 0, 2 and -1 in the strict comparison.

**Theorem 1.3 (Strict reversal in every dimension at least three).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Witness.witness_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GiniStationaryTest/Witness.witness_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

For every natural n at least three and every real t with 0<t<1, the tuple x=(t,1,...,1) satisfies G_{2,-1}(x)<G_{1,0}(x). Put k=n-1. The arithmetic mean is (t+k)/(k+1), and the cube of G_{2,-1}(x) is t(t^2+k)/(1+kt). The factorization has positive right side: k is positive and both (t-1)^3 and t-k^2 are negative. Positive denominators and monotonicity of the real cube root give the strict comparison. The tuple and the unequal-parameter Gini expression are reused from the endpoint comparison module.

**Theorem 1.4 (Failure of universal comparison).**

Lean statement: `D5/S3/ArithSums/GiniStationaryTest/Witness.not_mem_Gamma`

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/GiniStationaryTest/Witness.not_mem_Gamma` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Grünwald; Zs. Páles (2024). *Comparison of Gini means with fixed number of variables*. URL: <https://arxiv.org/abs/2408.07658v1>.

*Commentary.*

For every natural n at least three, the parameter pair ((1,0),(2,-1)) does not belong to Gamma_n((0,infinity)). The preceding strict comparison at t=1/2 contradicts the defining comparison at every positive tuple.

## References

- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Witness.not_mem_Gamma`
- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Witness.sum_highTuple_rpow`
- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Witness.witness_comparison`
- Truth anchor: `D5/S3/ArithSums/GiniStationaryTest/Witness.witness_identity`
- Dependency: [D5/S3/ArithSums/GiniStationaryTest/Defs](Defs.md)
