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

Any upper bound B for normalized sigma on positive ordered residuals propagates to the joint fibre with the multiplicative factor 403/105.

**Theorem 1.5 (Exact abundancy threshold transfer).**

$$normalizedSigma5040GtTwoIff$$

*Proof.* Machine-checked in Lean as `D5.S3.Arith.Robin.Valuation5040.PrimeValuation5040Sigma.normalized_sigma_5040_gt_two_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the coprime residual fibre, exceeding the strict abundancy threshold 2 is equivalent to the residual normalized ratio exceeding 210/403.

## References

- Truth anchor: `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.normalized_sigma_5040_mul_of_coprime`
- Truth anchor: `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.normalized_sigma_of_jointFiber5040`
- Truth anchor: `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.normalized_sigma_of_jointFiber5040_le_of_ordered_bound`
- Truth anchor: `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.normalized_sigma_5040_gt_two_iff`
- Truth anchor: `D5/S3/Arith/Robin/Valuation5040/PrimeValuation5040Sigma.sigma_5040_mul_of_coprime`
- Dependency: [D5/S3/Arith/ExponentExchange/CoprimeNormalForm](../../ExponentExchange/CoprimeNormalForm.md)
- Dependency: [D5/S3/Arith/ExponentExchange/IntegerSwap](../../ExponentExchange/IntegerSwap.md)
- Dependency: [D5/S3/Arith/Robin/PrimeValuation5040Bridge](../PrimeValuation5040Bridge.md)
