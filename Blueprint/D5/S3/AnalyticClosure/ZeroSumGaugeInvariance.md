# Zero-Sum Gauge Invariance

## Abstract

A zero-sum local gauge shift leaves the global completion sum unchanged.

**Theorem 1.1 (Zero-sum shifts preserve the global sum).**

$$\forall V: \operatorname{Type}, localContribution, shift: V\to \mathbb{R}, \operatorname{Summable}(localContribution) \land \operatorname{Summable}(shift) \land \sigma_{v} shift(v) = 0 \Rightarrow \sigma_{v} (localContribution(v) + shift(v)) = \sigma_{v} localContribution(v).$$

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/ZeroSumGaugeInvariance.zero_sum_gauge_invariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local ledger is represented by an absolutely summable real family localContribution, and shift is another absolutely summable family. When the shift sums to zero, replacing each local term by localContribution plus shift preserves the global sum.

## References

- Truth anchor: `D5/S3/AnalyticClosure/ZeroSumGaugeInvariance.zero_sum_gauge_invariance`
