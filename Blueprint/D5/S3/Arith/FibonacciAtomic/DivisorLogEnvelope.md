# The Divisor Logarithmic Envelope

## Abstract

The actual Moebius logarithmic divisor sum has a sharp positive envelope.

**Definition 1.1 (The actual signed divisor sum).**

$$\forall R\in\mathbb{N},t\in\mathbb{R},\operatorname{S}\left(R, t\right) = \sum_{d\in\operatorname{divisors}\left(R\right)}\operatorname{mu}\left(d\right)\cdot\operatorname{log}\left(1+t^{d}\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/DivisorLogEnvelope.moebiusLogSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural number R and real parameter t, S(R,t) is the finite sum over Nat.divisors R, denoted divisors(R) in the formula. For positive R these are exactly its positive natural divisors. Each coefficient is the integer ArithmeticFunction.moebius value cast to the reals, and log is the natural real logarithm. Nat.divisors 0 is empty. The envelope below concerns positive R and 0 < t <= 2/5.

**Theorem 1.2 (Positivity, the upper bound, and exact equality).**

$$\begin{aligned}\forall R\in\mathbb{N},t\in\mathbb{R},\\0<R\land0<t\le\frac{2}{5}\Rightarrow\\0<\operatorname{S}\left(R, t\right)\land\operatorname{S}\left(R, t\right)\le\operatorname{log}\left(1+t\right)\land(\operatorname{S}\left(R, t\right)=\operatorname{log}\left(1+t\right)\Leftrightarrow R=1)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/DivisorLogEnvelope.full_log_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural R and real t with R positive and 0 < t <= 2/5, the actual signed divisor sum is strictly positive and at most log(1+t). Equality holds if and only if R=1. Neither oddness nor squarefreeness is required; the squarefree odd case follows with the same sum, inequalities and equality condition.

Put f(d)=log(1+t^d). The elementary inequalities u/(1+u) <= log(1+u) <= u for u>0 and the bound on the absolute Moebius coefficient by one control every finite signed tail supported on d>=k by t^k/(1-t). The proof embeds its support into a finite integer interval and bounds the corresponding geometric sum.

After removing d=1, all divisors are at least two. Since t^2/(1-t) < t/(1+t) <= f(1), this tail cannot cancel the positive term f(1). If R>1, let p be its least prime divisor. Its coefficient is minus one. Every remaining divisor other than 1 and p exceeds p, so the remaining tail has absolute value at most t^(p+1)/(1-t) < t^p/(1+t^p) <= f(p). Thus the negative term at p gives S(R,t)<f(1). For R=1 the single divisor term is f(1).

The squarefree odd specialization is the positive logarithmic envelope in Section 382.2 of Fibonacci Atomic Relation Generation. The finite-tail estimate and least-prime deficit give the stated envelope for every positive natural modulus.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/DivisorLogEnvelope.full_log_envelope`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/DivisorLogEnvelope.moebiusLogSum`
