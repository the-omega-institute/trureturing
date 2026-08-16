# Positive Series Tails

## Abstract

A positive tail term makes the total exceed its finite partial sum.

**Theorem 1.1 (A positive tail forces a strict partial-sum bound).**

$$((\forall n, 0 \leq a_n) \land \operatorname{Summable}(a) \land (\exists i \in W^c, 0 < a_i)) \Rightarrow \sum_{n \in W} a_n < \sum_{n=0}^{\infty} a_n$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/PositiveSeriesTail.finite_partial_sum_lt_tsum_of_pos_outside` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a be a nonnegative summable real sequence and W a finite set of indices. If some strictly positive term lies outside W, then the sum over W is strictly smaller than the infinite sum of the sequence.

The proof truncates the sequence to W and applies Mathlib's strict comparison theorem Summable.tsum_lt_tsum_of_nonneg at the omitted positive index. The infinite sum of the truncation is then rewritten as the finite sum over W.

This closes only the positive-series strictness used to exclude a finite partial sum as the final value in remark 27.193. It makes no claim about the even-insertion formula, the reported numerical mean, or higher-order families in that atom.

## References

- Truth anchor: `D5/S3/AnalyticClosure/PositiveSeriesTail.finite_partial_sum_lt_tsum_of_pos_outside`
