# Capture Count Moments

## Abstract

The capture-count second moment and variance are exact one- and two-address sums.

**Theorem 1.1 (Exact capture-count second moment and variance).**

$$\operatorname{E}(N^{2})=\sum_{a}\operatorname{captureProbability}\left(q, f, a\right)+2*\operatorname{pairProbabilitySum}\left(q, f\right) \land \operatorname{Var}(N)=\sum_{a}\operatorname{captureProbability}\left(q, f, a\right)+2*\operatorname{pairProbabilitySum}\left(q, f\right)-{\sum_{a}\operatorname{captureProbability}\left(q, f, a\right)}^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S0/Diagonal/Probability/CaptureCountMoments.capture_count_second_moment_and_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N count addresses satisfying the frozen Captured predicate. Its second moment is the sum of the existing one-address capture probabilities plus twice the existing unordered two-address probability sum. Subtracting the square of the frozen mean gives the centered variance.

CaptureSecondMoment already proves the expectation identity and the Paley-Zygmund lower bound, so neither is redeclared. This theorem evaluates that bound's abstract second-moment denominator exactly; the resulting probability inequality is an exact re-expression, not a stronger inequality.

Repository search found no prior one-plus-two-address moment expansion. Pinned Mathlib supplies finite sum-product rearrangements, which the Lean proof applies to the existing capture indicators.

## References

- Truth anchor: `D5/S0/Diagonal/Probability/CaptureCountMoments.capture_count_second_moment_and_variance`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni](../../Asymptotics/WeightedProbability/FiniteBonferroni.md)
- Dependency: [D5/S0/Diagonal/Probability/CaptureSecondMoment](CaptureSecondMoment.md)
