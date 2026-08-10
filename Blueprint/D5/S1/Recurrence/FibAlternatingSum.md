# Alternating Fibonacci Sum

## Abstract

The parity-descending Fibonacci sum equals the next source-indexed Fibonacci number minus one.

**Theorem 1.1 (Alternating Fibonacci sum).**

$$\operatorname{alternatingFibSum}(k)=\operatorname{srcFib}(k+1)-1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/FibAlternatingSum.alternating_fibonacci_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the source convention F_0 = F_1 = 1, represented by srcFib(k) = fib(k+1). The function alternatingFibSum takes every other term descending from k: it is empty at k = 0, equals srcFib(1) at k = 1, and satisfies alternatingFibSum(k+2) = srcFib(k+2) + alternatingFibSum(k). For every natural k, this full parity-descending sum is exactly srcFib(k+1) - 1.

## References

- Truth anchor: `D5/S1/Recurrence/FibAlternatingSum.alternating_fibonacci_sum`
