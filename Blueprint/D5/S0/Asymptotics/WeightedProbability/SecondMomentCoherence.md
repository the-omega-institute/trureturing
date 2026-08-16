# Second Moment Coherence

## Abstract

The exact finite capture-count distribution reproduces its independently frozen second moment.

**Theorem 1.1 (Second moment agreement for the exact capture-count distribution).**

$$(\forall b, y,\ 0\leq q_{b}(y)) \land (\forall b,\ \sum_{y} q_{b}(y) = 1) \Rightarrow \sum_{0\leq j\leq \lvert A \rvert} j^{2} \sum_{S\subseteq A, \lvert S \rvert= j} \sum_{U\subseteq {A\setminus S}} (-1)^{\lvert U \rvert} \prod_{b\in A} \operatorname{if}\left(b\in \operatorname{union}\left(S, U\right), \operatorname{fixedPowerMass}\left(q, f, b, \lvert \operatorname{union}\left(S, U\right) \rvert\right), \operatorname{collisionPowerMass}\left(q, f, b, \lvert \operatorname{union}\left(S, U\right) \rvert\right)\right) = \sum_{a\in A} \operatorname{captureProbability}\left(q, f, a\right) + 2 \operatorname{pairProbabilitySum}\left(q, f\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/SecondMomentCoherence.exact_capture_count_probability_second_moment_agreement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit alternating-product law selects the unique realized count for each sample, and the squared cardinality is rewritten as the square of its capture-indicator sum.

The resulting weighted sum is identified with the independently frozen indicator-square second moment, which expands as the one-address probability sum plus twice the unordered two-address sum.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/SecondMomentCoherence.exact_capture_count_probability_second_moment_agreement`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/CaptureCountCoherence](CaptureCountCoherence.md)
- Dependency: [D5/S0/Diagonal/Probability/CaptureCountMoments](../../Diagonal/Probability/CaptureCountMoments.md)
