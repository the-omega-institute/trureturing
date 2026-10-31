# The 5040 valuation sigma factor

## Abstract

The 5040 valuation fibre contributes an exact normalized divisor-sum factor.

**Theorem 1.1 (Raw divisor-sum factorization).**

$$sigma5040MulOfCoprime$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.sigma_5040_mul_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If n is coprime to 210, multiplicativity gives sigma(5040 n) = 19344 sigma(n).

**Theorem 1.2 (Normalized 5040 factorization).**

$$normalizedSigma5040MulOfCoprime$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.normalized_sigma_5040_mul_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero residual n coprime to 210, the normalized ratio splits as sigma(5040 n)/(5040 n) = (403/105) sigma(n)/n.

Under exactly these hypotheses, put r = sigma(n)/n. Since 403/105 is positive, the factorization gives sigma(5040 n)/(5040 n) > 2 if and only if r > 2*(105/403) = 210/403. This is an application of normalized_sigma_5040_mul_of_coprime and ordered-field arithmetic; it preserves the nonzero and coprime-to-210 assumptions.

The strict threshold equivalence is an exact rescaling and supplies no upper bound for the residual ratio. The conditional ordered bound below still requires its separate bound B for every positive residual m coprime to 210 satisfying AllowedOrdered 210 m. Neither the threshold equivalence nor the finite factor supplies that bound, a Robin inequality, or an RH implication.

**Theorem 1.3 (Normalized factor on the exact valuation fibre).**

$$normalizedSigmaOfJointFiber5040$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.normalized_sigma_of_jointFiber5040` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The 5040 joint-fibre hypotheses supply the residual nonzeroness and coprimality, so the same exact factorization applies on the fibre.

**Theorem 1.4 (Conditional Robin reduction on the 5040 fibre).**

$$normalizedSigmaOfJointFiber5040LeOfOrderedBound$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.normalized_sigma_of_jointFiber5040_le_of_ordered_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any upper bound B for normalized sigma on positive ordered residuals propagates to the joint fibre with the multiplicative factor 403/105. Explicitly, B is real and the hypothesis is universal: for every natural m, if 1 <= m, m.Coprime 210, and AllowedOrdered 210 m, then sigma(m)/m <= B. With W coprime to each of 2,3,5,7 and jointFiber primes5040 profile5040 W (5040*n), the conclusion is sigma(5040*n)/(5040*n) <= (403/105)*B.

## References

- Truth anchor: `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.normalized_sigma_5040_mul_of_coprime`
- Truth anchor: `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.normalized_sigma_of_jointFiber5040`
- Truth anchor: `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.normalized_sigma_of_jointFiber5040_le_of_ordered_bound`
- Truth anchor: `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.sigma_5040_mul_of_coprime`
- Dependency: [D5/S3/Arith/ExponentExchange/CoprimeNormalForm](../../ExponentExchange/CoprimeNormalForm.md)
- Dependency: [D5/S3/Arith/ExponentExchange/IntegerSwap](../../ExponentExchange/IntegerSwap.md)
- Dependency: [D5/S3/Arith/Robin/PrimeValuation5040Bridge](../PrimeValuation5040Bridge.md)
