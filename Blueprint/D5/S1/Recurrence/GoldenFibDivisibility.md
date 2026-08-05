# Fibonacci Divisibility and Indices

## Abstract

Fibonacci divisibility detects divisibility of indices from index three onward.

**Theorem 1.1 (Fibonacci divisibility detects index divisibility).**

$$a \ge 3 \implies \left(F_a \mid F_b \iff a \mid b\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/GoldenFibDivisibility.fib_dvd_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural indices a and b with a at least three, the Fibonacci number F_a divides F_b exactly when a divides b. The lower bound removes the exceptional index two, where F_2 equals one.

## References

- Truth anchor: `D5/S1/Recurrence/GoldenFibDivisibility.fib_dvd_iff`
