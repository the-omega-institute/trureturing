# Normative Scale Choice Nonuniqueness

## Abstract

Two positive rescalings preserve both doctrines' internal rankings but produce opposite equiprobable aggregate choices.

**Theorem 1.1 (Positive cross-doctrine rescaling reverses the selected action).**

$$\begin{gathered}\exists alphaFirst, betaFirst, alphaSecond, betaSecond \in \mathbb{R},\\{}0 < alphaFirst \land 0 < betaFirst \land 0 < alphaSecond \land 0 < betaSecond,\\{}u(alphaFirst, betaFirst, first, a) > u(alphaFirst, betaFirst, first, b) \land u(alphaFirst, betaFirst, second, b) > u(alphaFirst, betaFirst, second, a),\\{}\forall d, x, y, (u(alphaFirst, betaFirst, d, x) > u(alphaFirst, betaFirst, d, y)) \iff (u(alphaSecond, betaSecond, d, x) > u(alphaSecond, betaSecond, d, y)),\\{}EU(alphaFirst, betaFirst, a) > EU(alphaFirst, betaFirst, b) \land EU(alphaSecond, betaSecond, b) > EU(alphaSecond, betaSecond, a).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValueScale/NormativeScaleChoiceNonuniqueness.normative_scale_choice_nonuniqueness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness uses the source carrier of two Boolean doctrines and two Boolean actions. The probability function is constantly one half, and the utility coordinates are alpha for the first doctrine's preferred action and beta for the second's.

The public statement quantifies the two positive scale pairs, exposes all within-doctrine comparisons as invariant, and states the two opposite strict aggregate inequalities. It introduces no metanormative record or permission-intersection consequence.

The qualitative list of possible metanormative decision principles is not promoted to inert formal fields. Repository search found the frozen arithmetic reversal theorem as the exact primitive, which is applied directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValueScale/NormativeScaleChoiceNonuniqueness.normative_scale_choice_nonuniqueness`
- Dependency: [D5/S3/ConceptDynamics/DecisionValue/NormativeScaleChoiceReversal](../DecisionValue/NormativeScaleChoiceReversal.md)
