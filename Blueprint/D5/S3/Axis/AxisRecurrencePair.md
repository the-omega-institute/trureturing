# Axis Recurrence Pair

## Abstract

The partial sum and the weight satisfy their two recurrences together.

The axis partial sum collects the legal words up to a given digit depth, and the axis weight reads the two Galois embeddings at that depth. Each satisfies its own two step recurrence: the sum steps by adding the sum two depths back, weighted by the next weight, and the weights compose multiplicatively.

Both halves were already proved separately. What did not exist was a statement that they hold of the same pair of sequences at the same depth, which is what the source records as one closed recurrence. Neither half is restated here; the conjunction is the content.

**Theorem 1.1 (The two recurrences hold of the same pair).**

$$\operatorname{W}\left(K + 2\right) = \operatorname{W}\left(K + 1\right) + \operatorname{t}\left(K + 2\right) \cdot \operatorname{W}\left(K\right) \land \operatorname{t}\left(K + 2\right) = \operatorname{t}\left(K + 1\right) \cdot \operatorname{t}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisRecurrencePair.axis_recurrence_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum recurrence follows from splitting a legal word on its highest digit, which forces the digit below it to be empty; the weight recurrence follows because both embeddings satisfy the same quadratic, so their powers are additively Fibonacci and the exponential turns that into a product.

## References

- Truth anchor: `D5/S3/Axis/AxisRecurrencePair.axis_recurrence_pair`
