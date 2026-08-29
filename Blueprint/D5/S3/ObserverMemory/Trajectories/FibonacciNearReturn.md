# Fibonacci Near Return

## Abstract

Fibonacci times return the inverse-golden circle rotation with exact alternating defect.

**Theorem 1.1 (Fibonacci times have exact alternating return defect).**

$$T(x) = x+\frac{1}{\varphi} \operatorname{mod}(1),\ \varepsilon_{n} = \frac{F_{n}}{\varphi}-F_{n-1},\ \forall n\in\mathbb{N}, \forall x\in\mathbb{R}/\mathbb{Z},\ \operatorname{iterate}(T, F_{n}, x) = x+\varepsilon_{n} \land\ \forall n\in\mathbb{N}, 1\le n,\ \varepsilon_{n} = (-1)^{n-1}\varphi^{-n} \land\ \forall n\in\mathbb{N}, 1\le n,\ \left|\varepsilon_{n}\right| = \varphi^{-n} \land\ \lim_{n\to\infty} \left|\varepsilon_{n}\right| = 0 \land\ \forall n\in\mathbb{N}, 1\le n,\ \operatorname{sgn}(\varepsilon_{n}) = (-1)^{n-1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/FibonacciNearReturn.fibonacci_near_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the additive circle modulo one, goldenRotation adds the reciprocal golden ratio. The real return defect at n is constructed as fib(n) divided by the golden ratio minus fib(n-1); it is not defined by the alternating-power conclusion.

For every positive Fibonacci index, the corresponding iterate is translation by that defect. The same public theorem gives its exact alternating inverse-golden form, its absolute value, convergence of the absolute defects to zero, and its alternating sign.

The proof applies the frozen D5 Fibonacci golden residual. Pinned Mathlib supplies additive-translation iterates, the additive-circle quotient criterion, geometric-power convergence, and sign multiplication. Searches found no exact theorem combining all five clauses.

The source's description of Fibonacci times as canonical return times is qualitative and has no in-scope predicate; the displayed mathematical clauses are formalized without inventing one.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/FibonacciNearReturn.fibonacci_near_return`
- Dependency: [D5/S1/Scale/FibonacciErrorRatio](../../../S1/Scale/FibonacciErrorRatio.md)
