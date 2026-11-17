# Prime-power exceptions and logarithmic shifts

## Abstract

The centered von Mangoldt function satisfies a quadratic relation outside a sparse set of proper prime powers.

**Theorem 1.1 (The quadratic relation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions.vonMangoldt_sub_one_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions.vonMangoldt_sub_one_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m that is not a prime power other than a prime, Y=Lambda(m)-1 satisfies Y squared=(log m-2)Y+log m-1. At primes Lambda(m)=log m, and at numbers that are not prime powers Lambda(m)=0. These two values give the relation, including m=0 and m=1.

**Theorem 1.2 (Counting the exceptions).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions.proper_prime_power_count_le_sqrt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions.proper_prime_power_count_le_sqrt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a nonnegative real constant C such that for every real x at least two, the number of natural m with 0<m<=x that are prime powers and are not primes is at most C times sqrt x. Each such m contributes at least log 2 to the sum of Lambda over nonprimes. This sum equals psi(x)-theta(x), which is bounded by a constant times sqrt x.

**Theorem 1.3 (Replacing a shifted logarithm).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions.log_shift_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions.log_shift_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N>0, H>=0, M>=0 and let n,d be natural numbers with N<=n and d<=MH. Then the absolute difference between log(n+d) and log n is at most MH/N. Monotonicity makes the difference nonnegative; the inequality log(n+d)<=log n+d/n bounds it by d/n, and the scale and shift bounds give the stated estimate.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions.log_shift_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions.proper_prime_power_count_le_sqrt`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PrimePowerExceptions.vonMangoldt_sub_one_quadratic`
