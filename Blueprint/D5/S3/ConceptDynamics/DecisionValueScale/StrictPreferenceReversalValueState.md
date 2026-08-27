# Strict Preference Reversal Separates Value States

## Abstract

Opposite strict rankings on one option carrier require distinct temporal value states.

**Theorem 1.1 (A strict reversal excludes one time-invariant scalar value).**

$$\forall U: \operatorname{Type}, a, b: U, V_{0}, V_{1}: U \to \mathbb{R}, (V_{0}(a) > V_{0}(b) \land V_{1}(b) > V_{1}(a)) \Rightarrow V_{0} \neq V_{1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalValueState.strict_preference_reversal_changes_value_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both moments use the same option carrier and the same two options. Each moment has a real-valued function that faithfully represents its observed strict ranking.

The first function ranks a above b, while the second ranks b above a. If the functions were equal, asymmetry of the real strict order would give an immediate contradiction.

Their public inequality is exactly the value-state change forced by the source assumptions, and rules out a single time-invariant scalar representation of both moments.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalValueState.strict_preference_reversal_changes_value_state`
