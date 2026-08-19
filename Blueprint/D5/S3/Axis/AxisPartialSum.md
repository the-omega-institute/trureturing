# Axis Partial Sum

## Abstract

The legal-word partial sum satisfies the two-step trace recurrence.

Legal words of digit depth at most K are exactly the naturals below the Fibonacci number at K plus one, so the partial sum over words is a sum over an initial segment and needs no separate word type. That is what makes the recurrence a splitting of a range rather than a combinatorial argument about strings.

Splitting the range at the next Fibonacci number sorts words by their highest occupied digit. A word that uses digit K plus two starts there, and the greedy decomposition leaves a remainder below the Fibonacci number two steps down: using a digit forces its predecessor to stay empty. The weight of the head factors out, which is the recurrence.

**Theorem 1.1 (The partial sum satisfies the trace recurrence).**

$$\forall K\in \mathbb{N},\ W_{K+2} = W_{K+1} + t_{K+2} \cdot W_{K}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisPartialSum.axisPartialSum_succ_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The head weight is the axis weight at the highest digit, whose own multiplicative recurrence is proved separately.

## References

- Truth anchor: `D5/S3/Axis/AxisPartialSum.axisPartialSum_succ_succ`
- Dependency: [D5/S3/Axis/AxisTraceRecurrence](AxisTraceRecurrence.md)
