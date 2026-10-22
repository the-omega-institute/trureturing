# Robin response of the actual lcm

## Abstract

The Mertens third-theorem error controls the Robin response of the actual prefix lcm.

**Theorem 1.1 (Common Robin response).**

Lean statement: `D5/S3/Arith/Robin/LcmRobinResponse.common_robin_response`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LcmRobinResponse.common_robin_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real u>=10000, let D=Nat.lcmUpto floor(u). If divisorRatio(D)<=exp(gamma)*log(log(D)), then Mertens.E₃(u)>=-4/sqrt(u)-(psi(u)-u)/(u*log(u)). The proof writes sigma(D)/D as the exact Euler product over primes p<=u, using the lcm factorization and the finite geometric sum for each p-adic layer. The omitted layer contributes at most 4/sqrt(u): primes p<=sqrt(u) have tail below 1/u, and primes p>sqrt(u) have exponent one and are bounded by the reciprocal-square tail. The tangent inequality for log(log) bounds log(log(psi(u))) by its value at u plus (psi(u)-u)/(u*log(u)). Finally psi(u)=log(D), psi(u)<=u*log(u), and the weak Robin inequality is passed through the logarithm; expanding Mertens.E₃ gives the stated bound.

**Theorem 1.2 (Strict Robin violation from a negative Mertens response).**

Lean statement: `D5/S3/Arith/Robin/LcmRobinResponse.common_robin_response_contrapositive`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/LcmRobinResponse.common_robin_response_contrapositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real u>=10000, if Mertens.E₃(u)<-4/sqrt(u)-(psi(u)-u)/(u*log(u)), then D=Nat.lcmUpto floor(u) satisfies divisorRatio(D)>exp(gamma)*log(log(D)), 5040<D, log(D)=psi(u), and D<=exp(u*log(u)). This is the contrapositive of the common response theorem, together with the same lcm logarithm identities and the Chebyshev upper bound used above.

## References

- Truth anchor: `D5/S3/Arith/Robin/LcmRobinResponse.common_robin_response`
- Truth anchor: `D5/S3/Arith/Robin/LcmRobinResponse.common_robin_response_contrapositive`
- Dependency: [D5/S3/Arith/Robin/PrimeFiberPropagation](PrimeFiberPropagation.md)
