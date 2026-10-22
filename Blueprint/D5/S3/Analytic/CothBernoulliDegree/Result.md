# The derivative sign theorem

## Abstract

Derivative signs of the power-weighted hyperbolic cotangent remainder.

**Theorem 1.1 (The two derivative orders).**

Lean statement: `D5/S3/Analytic/CothBernoulliDegree/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/CothBernoulliDegree/Result.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m and n be natural numbers with m at least one and n at least two, and put M=m+2n. The signed remainder P is defined from coth(t)/t by subtracting its Bernoulli terms through index n and multiplying by (-1)^n t^m. Its derivative of order M-2 is strictly positive at every positive t. Its derivative of order M-1 fails to be strictly positive everywhere on the positive ray.

The partial-fraction formula and its differentiated series express these derivatives as positive multiples of rational-kernel derivatives. At order M-2 each kernel is strictly positive. The derivative series is summable, so its sum is strictly positive.

At t=5 pi/M, the derivative of order M-1 is at most -(M-1)!/(8 pi^(2n+1)). The first normalized summand is at most -1/8 by the phase and amplitude estimate. The remaining normalized summands are bounded above by a reciprocal-power tail of at most 1/16. Restoring the common positive factor gives the stated strictly negative value and hence the second clause.

## References

- Truth anchor: `D5/S3/Analytic/CothBernoulliDegree/Result.result`
- Dependency: [D5/S3/Analytic/CothBernoulliDegree/Kernel](Kernel.md)
- Dependency: [D5/S3/Analytic/CothBernoulliDegree/PartialFraction](PartialFraction.md)
