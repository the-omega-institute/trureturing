# Divisor polynomials along Fibonacci prime windows

## Abstract

Fibonacci prime-power windows are nonzero and exhaust every positive divisor.

Write p(i) for Nat.nth Nat.Prime i, beginning with p(0)=2. All indices are natural numbers and s is complex. The Fibonacci sequence has fib(0)=0 and fib(1)=1. Write Z(n,s) for the sum of d to minus s over the positive divisors of n, and factorization(n,p) for the multiplicity of p. The indicator is one on its set and zero elsewhere. The natural-indexed sum in the final clause denotes tsum.

**Definition 1.1 (The specified full window).**

$$\operatorname{M}\left(k\right) = \prod_{i < k} {\operatorname{p}\left(i\right)}^{\operatorname{fib}\left(k + 2\right) - 1}$$

*Formalization.* `D5/S3/Arith/DivisorGibbs/FullWindowDivisorBridge.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equivalently the product is over i in Finset.range k. For k=0 it is the empty product, equal to one.

**Theorem 1.2 (Euler factorization and cofinal finite sums).**

$$\left(\forall n \in \mathbb{N},\; \forall s \in \mathbb{C},\; 0 < n \Rightarrow \operatorname{Z}\left(n, s\right) = \prod_{p \in \operatorname{primeFactors}\left(n\right)} \sum_{j=0}^{\operatorname{factorization}\left(n, p\right)} {{p}^{-s}}^{j}\right) \land \left(\left(\left(\forall k \in \mathbb{N},\; \operatorname{M}\left(k\right) \neq 0\right) \land \left(\forall d \in \mathbb{N},\; 0 < d \Rightarrow \exists K \in \mathbb{N}, \forall k \in \mathbb{N},\; K \le k \Rightarrow d \mid \operatorname{M}\left(k\right)\right)\right) \land \left(\forall k \in \mathbb{N},\; \forall s \in \mathbb{C},\; \operatorname{Z}\left(\operatorname{M}\left(k\right), s\right) = \sum_{d \in \mathbb{N}} \operatorname{indicator}\left(\operatorname{divisors}\left(\operatorname{M}\left(k\right)\right), d\right) {d}^{-s}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DivisorGibbs/FullWindowDivisorBridge.finite_divisor_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Euler identity holds for every positive n and every complex s, including s=0. Each window is a product of nonzero prime powers. For each positive d, a single cutoff bounds both the indices of its prime factors and their multiplicities; every later Fibonacci window is divisible by d. The final clause extends each finite divisor sum by zero. These statements impose no convergence assumption on s and do not assert a limit outside an absolutely convergent half-plane.

## References

- Truth anchor: `D5/S3/Arith/DivisorGibbs/FullWindowDivisorBridge.M`
- Truth anchor: `D5/S3/Arith/DivisorGibbs/FullWindowDivisorBridge.finite_divisor_bridge`
- Dependency: [D5/S3/Arith/DivisorGibbs/CofinalDivisibility](CofinalDivisibility.md)
- Dependency: [D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct](FiniteDivisorEulerProduct.md)
