# Normative Scale Choice Reversal

## Abstract

Equal doctrine probabilities and fixed internal rankings do not determine a unique action across utility scales.

**Theorem 1.1 (Doctrine probability does not determine cross-scale choice).**

$$\begin{gathered}alphaFirst, betaFirst, alphaSecond, betaSecond \in \mathbb{R}, 0 < alphaFirst, 0 < betaFirst, 0 < alphaSecond, 0 < betaSecond,\\{}betaFirst < alphaFirst, alphaSecond < betaSecond,\\{}\forall d, p(d) = \frac{1}{2},\\{}u(alphaFirst, betaFirst, first, a) = alphaFirst, u(alphaFirst, betaFirst, first, b) = 0, u(alphaFirst, betaFirst, second, a) = 0, u(alphaFirst, betaFirst, second, b) = betaFirst,\\{}u(alphaSecond, betaSecond, first, a) = alphaSecond, u(alphaSecond, betaSecond, first, b) = 0, u(alphaSecond, betaSecond, second, a) = 0, u(alphaSecond, betaSecond, second, b) = betaSecond,\\{}\forall d, x, y, (u(alphaFirst, betaFirst, d, x) > u(alphaFirst, betaFirst, d, y)) \iff (u(alphaSecond, betaSecond, d, x) > u(alphaSecond, betaSecond, d, y)),\\{}EU(alphaFirst, betaFirst, a) = \frac{alphaFirst}{2}, EU(alphaFirst, betaFirst, b) = \frac{betaFirst}{2},\\{}EU(alphaSecond, betaSecond, a) = \frac{alphaSecond}{2}, EU(alphaSecond, betaSecond, b) = \frac{betaSecond}{2},\\{}EU(alphaFirst, betaFirst, a) > EU(alphaFirst, betaFirst, b) \land EU(alphaSecond, betaSecond, b) > EU(alphaSecond, betaSecond, a).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/NormativeScaleChoiceReversal.normative_scale_choice_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public model has two Boolean doctrines and two Boolean actions. Both doctrines retain probability one half under both utility scales.

The first doctrine assigns positive utility only to action a, while the second assigns positive utility only to action b. All pairwise within-doctrine comparisons are identical across the two positive scale pairs.

The probability-weighted values are alpha over two and beta over two. Opposite cross-doctrine magnitudes therefore select action a under the first scaling and action b under the second.

Repository and pinned-library searches found no exact theorem. The construction uses ordered-field arithmetic directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/NormativeScaleChoiceReversal.normative_scale_choice_reversal`
