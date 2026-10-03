# Local Divisor Factors on a Factorial Congruence Class

## Abstract

Factorial congruences control normalized divisor factors at every prime below the factorial boundary.

**Definition 1.1 (Small-prime divisor weight).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer.smallWeight`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer.smallWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural m and n, smallWeight(m,n) is the product of reciprocalGeomSum(p,v_p(n)) over all primes p with 0 < p <= m. The reciprocal geometric sum ranges over i from zero through v_p(n) with term p^(-i); v_p(n) is the natural prime factorization exponent.

**Definition 1.2 (Factorial error floor).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer.delta`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer.delta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real product delta(m) ranges over primes p with 0 < p <= m, with factor 1 - p^(-v_p(m!)-1).

**Theorem 1.3 (Uniform local-factor squeeze and vanishing error).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m >= 2 and every pair of positive natural numbers a and b congruent modulo m!, the ratio smallWeight(m,a)/smallWeight(m,b) lies between delta(m) and the inverse of delta(m). For every natural m >= 4, the sum of p^(-v_p(m!)-1) over primes p <= m is at most 1/sqrt(m) + 1/(sqrt(m)-1). As m tends to infinity through the natural numbers, delta(m)-1 is O(1/sqrt(m)).

At each prime the congruence preserves valuations below v_p(m!); otherwise both valuations are at least this value. The geometric formula gives both ratio bounds. Powers of p below m divide m!, so each omitted local tail is at most 1/m. Split at floor(sqrt(m)): there are at most sqrt(m) smaller primes, while the larger tails are bounded by 1/(p(p-1)). Their sum telescopes after extending it to all integers above the cutoff. The product of 1 minus the tails is at least one minus their sum.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer.delta`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightTransfer.smallWeight`
- Dependency: [D5/S3/Arith/RobinExponentSwap](../RobinExponentSwap.md)
