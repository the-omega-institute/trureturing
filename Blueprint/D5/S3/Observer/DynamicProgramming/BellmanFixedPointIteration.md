# Active Bellman Fixed Point and Value Iteration

## Abstract

A contractive active Bellman operator has one value and geometric iteration.

**Theorem 1.1 (The active Bellman value is unique and reached geometrically).**

$$\begin{gathered}\forall V, I: \operatorname{Type}, \operatorname{CompleteMetricSpace}\left(V\right), \operatorname{Nonempty}\left(V\right), \operatorname{SemilatticeInf}\left(V\right),\\{}\operatorname{FiniteNonempty}\left(I\right), G: V, Q: I \to V \to V,\\{}T(v) := \operatorname{min}\left(G, \operatorname{inf}_i\in I Q(i)(v)\right), 0 < \gamma < 1,\\{}\operatorname{LipschitzWith}\left(\gamma, T\right) \Rightarrow\\{}\operatorname{ContractingWith}\left(\gamma, T\right) \land\\{}\exists v_*: V, T(v_*) = v_* \land\\{}(\forall w: V, T(w) = w \Rightarrow w = v_*) \land\\{}\forall v_0: V, n\in \mathbb{N},\\{}\operatorname{dist}\left(T^{n}(v_0), v_*\right) \le \gamma^{n} \operatorname{dist}\left(v_0, v_*\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/BellmanFixedPointIteration.bellman_contraction_unique_fixed_point_and_iteration_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value carrier is an arbitrary complete metric semilattice. For bounded belief-value functions this lattice infimum is pointwise minimum, so T(v) is constructed as the minimum of the stopping value G and the least continuation Q_i(v).

The displayed Lipschitz premise is the contraction estimate established immediately before the source theorem: every continuation changes future value by at most the discount factor. Together with gamma strictly below one it makes the constructed T a strict contraction.

Mathlib's canonical contraction fixed point supplies v star and proves that every other fixed value equals it. Iterating the Lipschitz estimate and using that every iterate fixes v star gives exactly the stated gamma-to-n distance bound for every initial value.

## References

- Truth anchor: `D5/S3/Observer/DynamicProgramming/BellmanFixedPointIteration.bellman_contraction_unique_fixed_point_and_iteration_bound`
