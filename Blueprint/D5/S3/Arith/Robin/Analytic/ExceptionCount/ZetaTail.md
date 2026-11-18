# Uniform control of omitted Euler factors

## Abstract

The logarithm of the omitted prime Euler factors has a power-decaying bound uniform over every fixed real zeta-parameter gap.

**Theorem 1.1 (A tail uniform over an unbounded parameter interval).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ZetaTail.uniform_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/ZetaTail.uniform_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every delta>0 there is a nonnegative C such that, for every real kappa>=1+delta and P>=2, log(zeta(kappa))+sum_{p<=P}log(1-p^(-kappa)) is at most C*P^(-delta/2). The real part of the complex zeta value is used. The existing convergent Euler-log identity expresses the difference as the sum over omitted primes. Each summand is bounded by 2*p^(-kappa); splitting its decay into P^(-delta/2) times the summable weight p^(-(1+delta/2)) gives one constant independent of both kappa and P. The exponent loss preserves uniformity throughout the unbounded interval. This controls the extra Euler factor in the real-power Robin exception reduction.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ZetaTail.uniform_tail`
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion](../LcmPowerEndpointExpansion.md)
