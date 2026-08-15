# Capture Count Coherence

## Abstract

The exact finite capture-count distribution is coherent with total mass and its independently computed mean.

**Theorem 1.1 (Normalization of the exact capture-count distribution).**

$$(\forall b,\ \sum_{y} q_{b}(y) = 1) \Rightarrow \sum_{0\leq j\leq \lvert A \rvert} \sum_{S\subseteq A, \lvert S \rvert= j} \sum_{U\subseteq {A\setminus S}} (-1)^{\lvert U \rvert} \prod_{b\in A} \operatorname{if}\left(b\in \operatorname{union}\left(S, U\right), \operatorname{fixedPowerMass}\left(q, f, b, \lvert \operatorname{union}\left(S, U\right) \rvert\right), \operatorname{collisionPowerMass}\left(q, f, b, \lvert \operatorname{union}\left(S, U\right) \rvert\right)\right) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/CaptureCountCoherence.exact_capture_count_probability_normalizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rewriting every explicit mass by the frozen exact capture-count theorem reduces the sum to a partition of all samples by their unique realized count.

The count lies between zero and |A|, so exactly one term survives; the frozen total sample-weight identity then gives one.

**Theorem 1.2 (Mean agreement for the exact capture-count distribution).**

$$(\forall b, y,\ 0\leq q_{b}(y)) \land (\forall b,\ \sum_{y} q_{b}(y) = 1) \Rightarrow \sum_{0\leq j\leq \lvert A \rvert} j \sum_{S\subseteq A, \lvert S \rvert= j} \sum_{U\subseteq {A\setminus S}} (-1)^{\lvert U \rvert} \prod_{b\in A} \operatorname{if}\left(b\in \operatorname{union}\left(S, U\right), \operatorname{fixedPowerMass}\left(q, f, b, \lvert \operatorname{union}\left(S, U\right) \rvert\right), \operatorname{collisionPowerMass}\left(q, f, b, \lvert \operatorname{union}\left(S, U\right) \rvert\right)\right) = \sum_{a\in A} \operatorname{captureProbability}\left(q, f, a\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/CaptureCountCoherence.exact_capture_count_probability_mean_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit law again selects the unique realized count for each sample, and the cardinality is rewritten as the sum of its capture indicators.

The resulting weighted indicator sum is identified with the independently frozen first-moment calculation from CaptureSecondMoment.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/CaptureCountCoherence.exact_capture_count_probability_mean_agreement`
- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/CaptureCountCoherence.exact_capture_count_probability_normalizes`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/ExactCaptureCount](ExactCaptureCount.md)
- Dependency: [D5/S0/Diagonal/Probability/CaptureSecondMoment](../../Diagonal/Probability/CaptureSecondMoment.md)
