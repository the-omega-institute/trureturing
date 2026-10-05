# Fibonacci Rank Size Decomposition

## Abstract

A common index splits the Fibonacci Euler ratio into small ranks and a bounded tail.

F(d) is the d-th Fibonacci number, phi is Euler's totient, and tau(j) counts the positive divisors of j. The cutoff Y is real. A multiplies F(d) over all positive divisors d of j with d <= Y.

**Theorem 1.1 (Small ranks and the remaining Euler logarithm).**

$$\begin{aligned}\forall j \in \mathbb{N}, Y \in \mathbb{R}, j \ge 3, Y \ge 5,\\A = \prod_{d \mid j, d \le Y} F\left(d\right) \ge 2 \Rightarrow \exists R \in \mathbb{R}:\\\frac{F\left(j\right)}{\phi\left(F\left(j\right)\right)} = \frac{A}{\phi\left(A\right)}\exp\left(R\right), 0 \le R \le \frac{6\tau\left(j\right)(1+\log\left(Y\right))}{Y}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/FibonacciRankSizeDecomposition.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural j >= 3 and real Y >= 5 with A >= 2, the Euler ratio of F(j) factors into the Euler ratio of A and the exponential of a nonnegative remainder R.

A prime divides A exactly when it divides F(j) and its first positive Fibonacci zero index is at most Y. Thus the prime support of A gives precisely the small-rank Euler factors. This uses the ranks of the primes, without a divisibility hypothesis between A and F(j).

The remaining primes group by their first zero indices d, each a divisor of j greater than Y. Each group has Euler logarithm at most 6*(1+log(d))/d. The decrease of (1+log(x))/x for x > 1 and the divisor count bound give the stated bound on R.

## References

- Truth anchor: `D5/S3/Arith/Robin/FibonacciRankSizeDecomposition.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/TimeSampling](../FibonacciAtomic/TimeSampling.md)
- Dependency: [D5/S3/Arith/Robin/FibonacciRankEulerTail](FibonacciRankEulerTail.md)
