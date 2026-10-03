# Fibonacci Rank Euler Tail

## Abstract

Primes with one Fibonacci entry index have a harmonic Euler logarithm bound.

For a natural index d, B(d) is the finite set of prime divisors p of F(d) such that p divides no F(k) with 1 <= k < d. Thus B(d) contains every prime with first positive Fibonacci zero at d, with each prime counted once. H(d) is the sum of 1/k for 1 <= k <= d.

**Theorem 1.1 (Complete prime bucket bound).**

$$\begin{aligned}\forall d \in \mathbb{N}, 5 < d \Rightarrow\\\sum_{p \in B\left(d\right)} \log\left(\frac{p}{p-1}\right) \le \frac{6H\left(d\right)}{d} \le \frac{6(1+\log\left(d\right))}{d}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/FibonacciRankEulerTail.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index d is any natural number greater than five. The sum ranges over the whole bucket, counting each prime once without a cutoff on its size.

The product of the distinct bucket primes divides F(d), so the number of primes is less than d. The Fibonacci rank theorem places every prime in one of the progressions k*d+1 and k*d-1. Primes at most d squared contribute at most 4*H(d)/d, while all larger primes contribute at most 1/d. The harmonic number bound gives the second inequality.

This estimates logarithms of Euler factors for one entry index. It makes no Robin inequality or Riemann hypothesis claim.

## References

- Truth anchor: `D5/S3/Arith/Robin/FibonacciRankEulerTail.result`
