# Robin response of the actual lcm

## Abstract

A negative Mertens response gives a strict Robin violation at the actual prefix lcm.

**Theorem 1.1 (Strict Robin violation from a negative Mertens response).**

Lean statement: `D5/S3/Arith/Robin/LcmRobinResponse.common_robin_response`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LcmRobinResponse.common_robin_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real u>=10000, if Mertens.E₃(u)<-4/sqrt(u)-(psi(u)-u)/(u*log(u)), then D=Nat.lcmUpto floor(u) satisfies divisorRatio(D)>exp(gamma)*log(log(D)), 5040<D, log(D)=psi(u), and D<=exp(u*log(u)). Here gamma is the real Euler constant and divisorRatio(D)=sigma(1,D)/D.

At price zero, golden_resource_objective_factorization and golden_resource_sigma_identity express log(sigma(D)/D) as the sum of local logarithms. Mathlib's factorization_lcmUpto and primeFactors_lcmUpto identify the actual exponents and prime support. Expanding Mertens.E₃ leaves the sum of logarithmic tails. For p<=sqrt(u) the tail factor is below 1/u; for p>sqrt(u) it is at most 1/p^2. The shared quadratic logarithm bound and Mertens.sum_one_div_sq_le bound the total by 4/sqrt(u).

The strict tangent loglog_tangent supplies the non-strict tangent bound by treating u=psi(u) separately. If D satisfied the weak Robin inequality, logarithmic monotonicity would force Mertens.E₃(u)>=-4/sqrt(u)-(psi(u)-u)/(u*log(u)), contradicting the premise. Mathlib's psi_eq_log_lcmUpto, endpoint divisibility, and Chebyshev's psi bound give the three accompanying witness facts.

## References

- Truth anchor: `D5/S3/Arith/Robin/LcmRobinResponse.common_robin_response`
- Dependency: [D5/S3/Arith/GoldenResourceObjectiveFactorization](../GoldenResourceObjectiveFactorization.md)
- Dependency: [D5/S3/Arith/Robin/LogarithmBounds](LogarithmBounds.md)
- Dependency: [D5/S3/Arith/Robin/PrimeFiberPropagation](PrimeFiberPropagation.md)
