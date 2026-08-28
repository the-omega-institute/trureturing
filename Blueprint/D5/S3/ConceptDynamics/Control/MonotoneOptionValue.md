# Monotone Option Value

## Abstract

A monotone future-value function preserves inclusion between post-action feasible futures.

**Theorem 1.1 (More feasible futures cannot have lower monotone value).**

$$\begin{gathered}\forall X, U, Z, L: \operatorname{Type},\\{}\operatorname{Preorder}\left(L\right), F: U \to X \to X,\\{}R: X \to Z \to Prop, W: \operatorname{Set}\left(Z\right) \to L,\\{}\operatorname{Monotone}\left(W\right), u, v: U, x: X,\\{}\{z: Z \mid R(F(v, x), z)\} \subseteq \{z: Z \mid R(F(u, x), z)\} \Rightarrow\\{}W(\{z: Z \mid R(F(v, x), z)\}) \leq W(\{z: Z \mid R(F(u, x), z)\}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/MonotoneOptionValue.monotone_option_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An action acts on the current state through F. Feasibility R then constructs the future-option set at the resulting state.

The public premises state that W is monotone on future sets and that every future feasible after v is also feasible after u.

Applying monotonicity to that inclusion gives the displayed value order. The option sets remain explicit constructions from the transition and feasibility primitives.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/MonotoneOptionValue.monotone_option_value`
