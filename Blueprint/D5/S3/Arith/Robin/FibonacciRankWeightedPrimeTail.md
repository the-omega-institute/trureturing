# Fibonacci Rank Weighted Prime Tail

## Abstract

The weighted prime Fibonacci first-rank tail is summable with an explicit cutoff bound.

For each prime p, z(p) is the least positive d with p dividing F(d). The cutoff y is real. Define w(y,p) as 1/(p*z(p)) when p is prime and p exceeds y, and zero otherwise.

**Theorem 1.1 (A uniform real-cutoff tail bound).**

$$\begin{aligned}\forall y \in \mathbb{R}, y \ge 2 \Rightarrow\\\operatorname{Summable}\left(w(y,\cdot)\right) \land \sum_{p \in \mathbb{N}} w\left(y, p\right) \le \frac{16}{\sqrt{y}}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/FibonacciRankWeightedPrimeTail.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Juan Jose Alba Gonzalez, Florian Luca, Carl Pomerance, and Igor E. Shparlinski (2012). *On numbers n dividing the nth term of a linear recurrence*. DOI: [10.1017/S0013091510001355](https://doi.org/10.1017/S0013091510001355). URL: <https://doi.org/10.1017/S0013091510001355>.

*Commentary.*

The sum over all natural p converges, and the displayed bound holds for every real y at least two. The first-zero buckets at ranks one through five are empty, empty, the singleton two, the singleton three, and the singleton five, respectively.

On a twofold interval with lower endpoint Y, split the primes according to whether z(p) is at most the square root of Y. For small ranks, a rank-d bucket has fewer than d primes, so each rank contributes at most 1/Y. There are at most the square root of Y such ranks. For large ranks, each term is at most 1/(Y*sqrt(Y)), and the interval has at most 2Y natural numbers. The total is at most 3/sqrt(Y).

Partitioning every finite prime sum into twofold intervals bounds it by a geometric series with ratio 1/sqrt(2). Its ratio is at most three quarters, giving a uniform bound of 12/sqrt(y), hence the displayed 16/sqrt(y). Nonnegative finite sums with this common bound establish summability and the infinite-sum inequality together.

The decay order y to the power minus one half is known from the twofold-interval argument in the proof of Theorem 1.2 in Alba Gonzalez, Luca, Pomerance and Shparlinski, On numbers n dividing the nth term of a linear recurrence, Proceedings of the Edinburgh Mathematical Society 55 (2012), 271-289. The explicit constant for all real y at least two is the FIB volume's deduction. No novelty claim is made.

## References

- Truth anchor: `D5/S3/Arith/Robin/FibonacciRankWeightedPrimeTail.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/TimeSampling](../FibonacciAtomic/TimeSampling.md)
- Dependency: [D5/S3/Arith/Robin/FibonacciRankEulerTail](FibonacciRankEulerTail.md)
