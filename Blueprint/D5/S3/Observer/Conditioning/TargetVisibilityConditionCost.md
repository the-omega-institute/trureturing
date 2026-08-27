# Target Visibility and Condition Cost

## Abstract

Exact target visibility carries a canonical target-specific condition cost.

**Theorem 1.1 (Visibility determines a unique minimum-norm cost certificate).**

$$\begin{gathered}\forall K, State, Observation: \operatorname{Type},\\{}\operatorname{RCLike}(K) \land \operatorname{NormedAddCommGroup}(State) \land \operatorname{InnerProductSpace}(K, State) \land \operatorname{FiniteDimensional}(K, State) \land\\{}\operatorname{NormedAddCommGroup}(Observation) \land \operatorname{InnerProductSpace}(K, Observation) \land \operatorname{FiniteDimensional}(K, Observation) \Rightarrow\\{}\forall M: \operatorname{LinearMap}(K, State, Observation), v: State,\\{}(\forall x, y: State, \operatorname{M}(x) = \operatorname{M}(y) \Rightarrow \langle v, x \rangle = \langle v, y \rangle) \iff (\exists! (s, a): State \times Observation,\\{}s \in (\ker(M))^{\perp} \land\\{}\operatorname{M^{*}}(a) = v \land\\{}a = \operatorname{M}(s) \land\\{}(\forall b: Observation, \operatorname{M^{*}}(b) = v \Rightarrow \left\lVert a \right\rVert \leq \left\lVert b \right\rVert) \land\\{}\left\lVert a \right\rVert^{2} = \langle v, s \rangle).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/TargetVisibilityConditionCost.target_visibility_condition_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The measurement map is defined on arbitrary finite-dimensional inner-product spaces over a real or complex scalar field. A target is exactly visible when its Riesz functional is constant on every measurement fiber.

The theorem constructs the state Gramian from the measurement and its adjoint. It then exposes the unique Gram preimage orthogonal to the hidden kernel and the induced observation coefficient.

That coefficient solves the adjoint equation, has minimum norm among all such solutions, and its squared norm equals the target quadratic form on the canonical Gram preimage. This is the target-specific condition cost without introducing a substitute pseudoinverse.

Pinned Mathlib supplies adjoint-range duality, equality of the Gram and adjoint ranges, orthogonal decomposition, and Pythagoras. Repository searches found no existing theorem combining all public clauses.

## References

- Truth anchor: `D5/S3/Observer/Conditioning/TargetVisibilityConditionCost.target_visibility_condition_cost`
