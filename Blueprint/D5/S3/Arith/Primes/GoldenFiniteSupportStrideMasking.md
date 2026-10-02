# Finite-support stride masking

## Abstract

Coupling and stride valuations jointly determine finite-support matrix periods.

**Theorem 1.1 (Exact period and first contribution).**

Lean statement: `D5/S3/Arith/Primes/GoldenFiniteSupportStrideMasking.golden_finite_support_stride_masking`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenFiniteSupportStrideMasking.golden_finite_support_stride_masking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a nonempty finite set of primes greater than five and assign each p in S a positive exponent a_p. Write pi(m) for the order of the Fibonacci matrix modulo m, pi_s(m) for the order of its s-th power, and h_p for the p-adic valuation of the Fibonacci number at the first positive index divisible by p. Set T to the least common multiple of the pi(p), beta_p to the p-adic valuation of T, and u_p to the p-adic valuation of a positive stride s. At the modulus obtained by multiplying the p-th prime powers p^a_p, the stride period equals T divided by gcd(T,s), times the product of p raised to the nonnegative part of a_p minus h_p minus max(beta_p,u_p). With all other support exponents set to one and p's exponent set to e, the stride period is the squarefree baseline period times p raised to the nonnegative part of e minus h_p minus max(beta_p,u_p). The prime p first increases the stride period beyond the squarefree baseline when its exponent exceeds h_p plus max(beta_p,u_p). Thus coupling and stride delays combine by their maximum.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenFiniteSupportStrideMasking.golden_finite_support_stride_masking`
- Dependency: [D5/S3/Arith/Primes/GoldenFiniteSupportSquarePeriod](GoldenFiniteSupportSquarePeriod.md)
