# Strict Preference Reversal Alternatives

## Abstract

A strict preference reversal forces a change in a determining state or a loss of behavioral fidelity.

**Theorem 1.1 (A strict reversal excludes one invariant scalar representation).**

$$\begin{gathered}\forall U, F, V, S, T, C: \operatorname{Type},\\{}a, b: U, f: F,\\{}v_{0}, v_{1}: V, s_{0}, s_{1}: S,\\{}t_{0}, t_{1}: T, c_{0}, c_{1}: F \to C,\\{}B_{0}, B_{1}: U \to \left(U \to \operatorname{Prop}\right), u: V \to \left(S \to \left(T \to \left(C \to \left(U \to \mathbb{R}\right)\right)\right)\right),\\{}(B_{0}(a, b) \land B_{1}(b, a)) \Rightarrow\\{}(\neg \exists w: U \to \mathbb{R}, ((\forall x, y: U, B_{0}(x, y) \Rightarrow w(x) > w(y)) \land (\forall x, y: U, B_{1}(x, y) \Rightarrow w(x) > w(y)))) \land\\{}(v_{0} \neq v_{1} \lor s_{0} \neq s_{1} \lor t_{0} \neq t_{1} \lor c_{0} \neq c_{1} \lor \neg ((\forall x, y: U, B_{0}(x, y) \Rightarrow u(v_{0}, s_{0}, t_{0}, c_{0}(f), x) > u(v_{0}, s_{0}, t_{0}, c_{0}(f), y)) \land (\forall x, y: U, B_{1}(x, y) \Rightarrow u(v_{1}, s_{1}, t_{1}, c_{1}(f), x) > u(v_{1}, s_{1}, t_{1}, c_{1}(f), y)))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalAlternatives.strict_preference_reversal_forces_state_change_or_behavioral_unfaithfulness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both observations use the same option carrier, the same two options, and the same fact. Their behavior relations rank the options in opposite directions.

No single real-valued function can respect both strict rankings. For a shared utility rule indexed by value, self, temporal, and context states, the reversal therefore forces one state to change or at least one behavior relation not to respect the induced strict ranking.

The proof applies the frozen strict-order reversal theorem both to the putative common scalar function and to the state-indexed utility after all four state coordinates are assumed unchanged.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalAlternatives.strict_preference_reversal_forces_state_change_or_behavioral_unfaithfulness`
- Dependency: [D5/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalValueState](StrictPreferenceReversalValueState.md)
