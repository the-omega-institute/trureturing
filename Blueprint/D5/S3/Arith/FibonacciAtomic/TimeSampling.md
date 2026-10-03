# Pairwise Fibonacci Time Recovery

## Abstract

The smallest prime zero rank bounds, and attains, the number of mutually recovering time observations.

N includes zero. F is the Fibonacci sequence with F(0)=0 and F(1)=1. The modulus n is a natural number, the state x=(a,b) lies in (Z/nZ)^2, and time labels are natural numbers. Finset(N) denotes finite sets of distinct time labels; range(k) is the set of labels from zero through k-1. All readout arithmetic is modulo n. Natural infima are zero on the empty set. On positive moduli a positive Fibonacci zero exists, since the invertible Fibonacci step permutes a finite state space.

**Definition 1.1 (Time readout).**

$$\operatorname{r}\left(n, t, x\right) = \operatorname{F}\left(t\right) a + \operatorname{F}\left(t+1\right) b$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TimeSampling.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The step sends (a,b) to (b,a+b). Its second coordinate after t steps is r(n,t,x).

**Definition 1.2 (Pairwise source recovery).**

$$\operatorname{P}\left(n, T\right) \Leftrightarrow \forall s \in T, \forall t \in T, (s<t) \implies \operatorname{Injective}\left(x \mapsto (\operatorname{r}\left(n, s, x\right),\operatorname{r}\left(n, t, x\right))\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TimeSampling.PairwiseRecovery` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Recovery means injectivity on the whole state space, with the two time labels retained.

**Definition 1.3 (Positive zero rank).**

$$\operatorname{z}\left(p\right) = \operatorname{inf}\left(\{d:N \mid 0<d \land p \mid \operatorname{F}\left(d\right)\}\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TimeSampling.zeroRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a prime p, z(p) is the least positive d such that p divides F(d).

**Definition 1.4 (The least prime zero rank).**

$$\operatorname{L}\left(n\right) = \operatorname{inf}\left(\{\operatorname{z}\left(p\right) \mid \operatorname{Prime}\left(p\right) \land p \mid n\}\right)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/TimeSampling.recoveryLimit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n at least two, its prime divisors form a nonempty finite set, so this infimum is a minimum.

**Theorem 1.5 (Sharp recovery capacity).**

$$\forall n \in N, (2 \le n) \implies (\operatorname{P}\left(n, \operatorname{range}\left(\operatorname{L}\left(n\right)\right)\right) \land (\forall T \in \operatorname{Finset}\left(N\right), \operatorname{P}\left(n, T\right) \implies \operatorname{card}\left(T\right) \le \operatorname{L}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/TimeSampling.pairwise_recovery_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two readings at s<t recover the source exactly when n and F(t-s) are coprime. For a prime divisor p attaining L(n), time labels in a recovering set must have distinct residues modulo z(p), which bounds the set size by L(n). Conversely, positive differences between labels in range(L(n)) are smaller than every prime zero rank. No prime divisor of n divides the corresponding Fibonacci number, so every pair recovers. Since range(L(n)) has L(n) elements, the upper bound is attained.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TimeSampling.PairwiseRecovery`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TimeSampling.pairwise_recovery_maximum`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TimeSampling.readout`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TimeSampling.recoveryLimit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/TimeSampling.zeroRank`
