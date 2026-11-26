# Uniform parameters for the signed character sieve

## Abstract

Uniform parameters for the signed character sieve

**Theorem 1.1 (Propagation of a strict logarithmic margin).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.margin_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SieveThreshold.margin_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If exp(2) ≤ x ≤ y and 2+3A log(x) < sqrt(x), then the same strict margin holds at y. No sign condition on A is required. For nonnegative A one applies the antitonicity of log(x)/sqrt(x); negative A gives the conclusion directly from sqrt(y)>2.

**Theorem 1.2 (A reusable exponential threshold).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.exp_two_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SieveThreshold.exp_two_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Whenever 7.4 ≤ x, exp(2) ≤ x. The numerical bound is the existing ThetaIntegrated99.exp_two_le theorem; transitivity transfers it to x.

**Theorem 1.3 (Splitting a prime support at an arbitrary rank).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.split_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SieveThreshold.split_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x>1 with r+s distinct prime factors in x-1, there are a nonzero divisor e of x-1 and a finite set T. Each prime divisor of x-1 divides e or lies in T. The support of e has r factors, T has s factors, and the sieve set is exactly T. The witnesses are normalized: e is the product of the first r ordered prime factors and T is the image of the last s factors. Its margin is one minus the reciprocal sum of the last s ordered prime factors.

**Theorem 1.4 (Converting a scalar margin to the signed sieve inequality).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.signed_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SieveThreshold.signed_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume x≥1, d>0, K≤dA and 2+3A log(x)<sqrt(x). Then K times (3/2)sqrt(x)log(x) is strictly less than d times (x/2-sqrt(x)). The nonnegative logarithmic error term preserves the coefficient bound.

**Definition 1.5 (Feasibility of the coarse signed sieve).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.Feasible`

*Formalization.* `D5/S3/Arith/PrimitiveRoot/SieveThreshold.Feasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Feasibility means that there are a nonzero parameter e and a finite set T covering every prime factor of x-1 absent from e, with a positive sieve margin. Writing U=sievePrimes(x,e,T), the signed error coefficient at gcd(e,x-1) times (3/2) sqrt(x) log(x) must be strictly less than delta(U) times (x/2-sqrt(x)). This is an arithmetic condition for arbitrary natural x.

**Theorem 1.6 (Uniform feasibility above 4100000).**

Lean statement: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.feasible_of_ge_4100000`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/PrimitiveRoot/SieveThreshold.feasible_of_ge_4100000` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural integer x at least 4100000 is feasible. No primality or GRH hypothesis occurs. With at most two distinct prime factors the sieve set is empty; with three through seven factors the prefix consists of the smallest two; above seven the largest six form the sieve set. The geometric radical lower bound and logarithmic monotonicity preserve strict positive margins for arbitrarily many factors. The companion theorem SieveThresholdExact.feasible_iff supplies the complete arithmetic classification from 3483481 onward: precisely 3483481 and 3573571 are infeasible. The number 4100000 is the start of this uniform tail argument.

## References

- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.Feasible`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.exp_two_le`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.feasible_of_ge_4100000`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.margin_mono`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.signed_margin`
- Truth anchor: `D5/S3/Arith/PrimitiveRoot/SieveThreshold.split_support`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Contact/ThetaIntegrated99](../Lattices/Klartag/Contact/ThetaIntegrated99.md)
- Dependency: [D5/S3/Arith/PrimitiveRoot/CharacterSieve](CharacterSieve.md)
- Dependency: [D5/S3/Arith/PrimitiveRoot/SievePrimeFactors](SievePrimeFactors.md)
