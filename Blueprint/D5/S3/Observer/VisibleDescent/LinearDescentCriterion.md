# Linear Descent Criterion

## Abstract

Bounded linear descent through an orthogonal visible projection is equivalent to vanishing hidden-to-visible carry and to projection-fiber dependence.

**Theorem 1.1 (Orthogonal projection descent and the cross block).**

$$\begin{gathered}\forall K, H: \operatorname{Type},\\{}[\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(K, H)], V: \operatorname{Submodule}(K, H), [\operatorname{HasOrthogonalProjection}(V)], T: \operatorname{ContinuousLinearMap}(K, H, H), P: \operatorname{ContinuousLinearMap}(K, H, H), Q: \operatorname{ContinuousLinearMap}(K, H, H),\\{}P = \operatorname{orthogonalProjectionOnto}(V), Q = \operatorname{starProjection}(V^{\perp}) \Rightarrow\\{}(\operatorname{TFAE}(\exists Tbar: V \to V, P \circ T = Tbar \circ P, P \circ T \circ Q = 0, \forall x, y: H, P(x) = P(y) \Rightarrow {P \circ T}(x) = {P \circ T}(y))) \land\\{}((P \circ T \circ Q = 0) \Rightarrow (P \circ T = \operatorname{restrictTo}(P \circ T, V) \circ P \land \forall Tbar: V \to V, (P \circ T = Tbar \circ P) \Rightarrow Tbar = \operatorname{restrictTo}(P \circ T, V))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/VisibleDescent/LinearDescentCriterion.linear_descent_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is a Hilbert space, V is an orthogonally complemented visible subspace, P is its bounded orthogonal projection, and Q is projection onto the orthogonal complement. The ambient dynamics T is bounded and linear.

A commuting descent kills PTQ because P vanishes on the Q-range. Conversely, PTQ equal to zero makes PT constant on every P-fiber, since the difference of two states in one fiber lies in the hidden subspace.

Fiber dependence constructs the descent by including a visible vector, applying T, and projecting back with P. Surjectivity of P onto V makes every other commuting descent equal to this explicit restriction.

## References

- Truth anchor: `D5/S3/Observer/VisibleDescent/LinearDescentCriterion.linear_descent_criterion`
- Dependency: [D5/S3/Observer/HiddenFlow/VisibleHiddenProjectionCriteria](../HiddenFlow/VisibleHiddenProjectionCriteria.md)
