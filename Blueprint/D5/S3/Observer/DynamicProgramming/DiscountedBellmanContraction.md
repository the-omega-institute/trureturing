# Discounted Bellman Contraction and Fixed Value

## Abstract

A finite-state finite-action discounted Bellman operator is a strict sup-norm contraction with a unique fixed value function.

**Theorem 1.1 (The discounted Bellman operator has one fixed value).**

$$\begin{gathered}\forall S, A: \operatorname{Type},\\{}\operatorname{FiniteNonempty}\left(S\right), \operatorname{DiscreteTopology}\left(S\right), \operatorname{FiniteNonempty}\left(A\right),\\{}r: S \times A \to \mathbb{R}, P: S \times A \times S \to \mathbb{R},\\{}\gamma: \operatorname{NNReal}, 0 < \gamma < 1,\\{}(\forall s\in S, a\in A, t\in S, 0 \leq P\left(s, a, t\right) \land \forall s\in S, a\in A, \sum_{t\in S} P\left(s, a, t\right) = 1) \Rightarrow \\{}(\forall v, w: \operatorname{BoundedContinuousFunctions}\left(S, \mathbb{R}\right), \left\lVert \operatorname{discountedBellmanOperator}\left(r, P, \gamma, v\right) - \operatorname{discountedBellmanOperator}\left(r, P, \gamma, w\right) \right\rVert \leq \gamma \left\lVert v - w \right\rVert) \land (\exists! v: \operatorname{BoundedContinuousFunctions}\left(S, \mathbb{R}\right), \operatorname{discountedBellmanOperator}\left(r, P, \gamma, v\right) = v).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/DiscountedBellmanContraction.discounted_bellman_contraction_and_unique_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the state and action spaces be finite and nonempty, with the state space discrete. Fix an arbitrary real reward, a nonnegative transition kernel whose weights sum to one for every state-action pair, and a discount factor gamma strictly between zero and one. The Bellman operator maximizes immediate reward plus discounted expected continuation value over all actions.

Each transition row is a probability distribution, so changing the value function changes every continuation expectation by at most the uniform distance between the two value functions. Multiplication by gamma gives the actionwise bound, and taking the finite action maximum preserves it. Thus the full Bellman operator is gamma-Lipschitz in the uniform norm.

Because gamma is strictly below one, this Lipschitz estimate is a strict contraction on the complete space of bounded continuous real-valued functions on the finite state space. The contraction fixed-point principle therefore supplies a fixed value function and forces every other fixed value function to equal it.

## References

- Truth anchor: `D5/S3/Observer/DynamicProgramming/DiscountedBellmanContraction.discounted_bellman_contraction_and_unique_fixed_point`
